open Pp
open CErrors
open Util
open Names
open Term
open Termops
open Constr
open Context
open EConstr
open Vars
open Namegen
open Inductiveops
open Printer
open Retyping
open Tacmach
open Tacticals
open Tactics
open Elim
open Equality
open Tactypes
open Proofview.Notations
open Auto
open Evd
open Coutils
open Micromega_plugin

module PV = Proofview

let ind_family_comp (indf1: inductive_family) (indf2: inductive_family) : int =
  let ((ind1, _), _) = dest_ind_family indf1 in
  let ((ind2, _), _) = dest_ind_family indf2 in
  let mc = MutInd.CanOrd.compare (fst ind1) (fst ind2) in
  if mc = 0 then
    Stdlib.compare (snd ind1) (snd ind2)
  else mc

(* is `t` an instance of an inductive proposition? destruct and return it if yes *)
let dest_inductive_prop env sigma t : inductive_type option =
  let resty = 
    try Some (find_rectype env sigma t)
    with | Not_found ->
      None
  in
  (* check if this is a prop *)
  Option.filter
    begin fun _ ->
      let mind = get_sort_of env sigma t in
      ESorts.is_prop sigma mind
    end
    resty

let is_inductive_prop env sigma t : bool =
  match dest_inductive_prop env sigma t with
  | Some _ -> true
  | None -> false

(* given a (constructor) type, extract argument types from it, and filter discovered inductive props from it *)
let dest_cons_inductives env sigma (ty: etypes) : inductive_family list =
  let (annotated_args, concl) = decompose_prod sigma ty in
  let args = List.map snd annotated_args in
  let ind_ty_args = (* set of ((ind, u), t) triples *)
    List.map_filter (dest_inductive_prop env sigma) args
  in
  let ind_fam_args = 
    List.map (fun (IndType (indf, _realargs)) -> indf) ind_ty_args
  in
    ind_fam_args

(* retrieve the types of constructors for an inductive family *)
let cons_types_of_family env _sigma (indf: inductive_family) : etypes list =
  let cons = Inductiveops.get_constructors env indf in
  let tarray = Array.map (fun cstr -> type_of_constructor env cstr.cs_cstr) cons in
  let tlist = Array.to_list tarray in
  tlist

(* find the inductive families backward-reachable from the constructors of an inductive family *)
let reachable_inductive_families env sigma (indf: inductive_family) : inductive_family list =
  let step_reachable_inductive_families (indfs: inductive_family list) : inductive_family list =
    indfs
      |> List.concat_map (cons_types_of_family env sigma)
      |> List.concat_map (dest_cons_inductives env sigma)
      |> List.append indfs (* ensure monotonicity *)
      |> List.sort_uniquize ind_family_comp (* keep set semantics *)
  in

  let rec fix f x = 
    let y = f x in
    if y = x then x else fix f y
  in

  step_reachable_inductive_families [indf]

(* collect the contstructor terms and their types for a list of inductive families *)
(* (econstr and etypes are actually the same type) *)
(* (used here just to distinguish what is used as a term and what as a type) *)
let cons_of_families env _sigma (indfs: inductive_family list) : (econstr * etypes) list =
  indfs 
    |> List.map begin fun indf ->
      let cons_summary = Inductiveops.get_constructors env indf in
      let consu = Array.map (fun cstr -> cstr.cs_cstr) cons_summary in
      (* actual constructor terms that can be applied *)
      let cons = Array.map (fun cstr -> EConstr.mkConstructU cstr) consu in
      (* their types, to construct clauses *)
      let cons_types = Array.map (type_of_constructor env) consu in
      List.combine (Array.to_list cons) (Array.to_list cons_types)
    end
    |> List.concat

(* create a mapping from (rocq) terms to internal terms *)
let rec constr_to_term env sigma vmap (tmap: constrtbl) (t: econstr) : Term.term * constrtbl =
  (* we assume a first-order abstraction over the terms *)
  (* functions are not checked or expanded further *)
  (* arguments are transformed recursively *)
  if isVar sigma t && List.mem_assoc t vmap then
    let vi = List.assoc t vmap in
    Term.Var vi, tmap
  else 
    let func, args = decompose_app sigma t in
    let fid = hashtbl_get_or_inc tmap func in
    let args_list = Array.to_list args in
    let args', tmap' = constr_list_to_term env sigma vmap tmap args_list in
    Term.Fun (fid, args'), tmap'
and constr_list_to_term env sigma vmap (tmap: constrtbl) (ts: econstr list) : Term.term list * constrtbl =
  let args', tmap' =
    List.fold_right (fun t (acc, tmap) -> 
      let (t', tmap') = constr_to_term env sigma vmap tmap t in
      (t' :: acc, tmap')
    ) ts ([], tmap)  
  in
  args', tmap'

(* create a mapping from terms to internal formulas *)
let rec constr_to_formula env sigma vmap (tmap: constrtbl) (t: econstr) : Term.formula * constrtbl =
  (* requires: the term is a prop possibly applied to something *)
  let func, args = decompose_app sigma t in
  let fid = hashtbl_get_or_inc tmap func in
  let args_list = Array.to_list args in
  let args', tmap' = constr_list_to_term env sigma vmap tmap args_list in
  Term.Atom ((Term.Predicate fid), args'), tmap'
and constr_list_to_formula env sigma vmap (tmap: constrtbl) (ts: econstr list) : Term.formula list * constrtbl =
  let args', tmap' =
    List.fold_right (fun t (acc, tmap) -> 
      let (t', tmap') = constr_to_formula env sigma vmap tmap t in
      (t' :: acc, tmap')
    ) ts ([], tmap)  
  in
  args', tmap'

(* construct an internal wrapped clause from a constructor type *)
let clause_of_type env sigma (tmap: constrtbl) (cstr_id: int) (ty: etypes)  : Prolog.clause * constrtbl =
  (*
    Process:

    - unfold product type
    - if this is a term param, give it a new id
    - if this is a prop, turn it into a formula
    - no terms should show up after any prop
    - there is a more precise fragment criterion we assume (unchecked):
      - prop terms are not proof dependant (i.e. on each other)
      - FOR NOW: some inductive param/concl explicitly depends on each term param 
  *)

  (* decompose the product type *)
  (* and separate the term arguments, i.e. non-props *)
  let (annotated_args, concl) = decompose_prod sigma ty in

  (* extract the term variables from this type*)
  let vs =
    annotated_args
    |> List.drop_while (is_inductive_prop env sigma << snd)
    |> List.map (binder_name << fst)
    |> List.map (function
      | Name.Name id -> mkVar id
      | Name.Anonymous -> failwith "TODO: Anonymous term binder in clause_of_type"
    )
  in

  (* recompute args after reducing term level quantifiers *)
  let (annotated_args, concl) = decompose_prod sigma (Reductionops.hnf_prod_applist env sigma ty vs) in

  (* 
    each annotated argument is a pair of (name, relevance) 
    
    name can be an actual `Name id` or `Anonymous`.
    
    TODO: unclear how to handle anonymous names in our context. Does a term
    parameter for an inductive prop constructor matter if you do not name and
    use it? Given that all types are known to be non-empty.

    The relevance is a wrapped `Sorts.relevance`, which tracks whether the
    parameter is proof relevant. This is not *us*-relevant, at least.
  *)

  (* all variables are local, and the formula is prenex
    so just store the variables and name them 0..n-1
  *)
  let prop_args = annotated_args
    |> List.rev
    |> List.drop_while (not << is_inductive_prop env sigma << snd)
    |> List.map snd 
    (* discarding names is fine if the inner terms are not dependent on us (shouldn't be) *)
  in

  let vmap =
    List.map_i (fun idx x -> x, idx) 0 vs
  in

  let empty_tmap = Hashtbl.create 32 in

  let to_form = constr_list_to_formula env sigma vmap in

  let clause_body, tmap' = constr_list_to_formula env sigma vmap tmap prop_args in
  let clause_head, tmap'' = constr_to_formula env sigma vmap tmap concl in

  Prolog.Clause (cstr_id, List.length vmap, clause_head, clause_body), tmap''

(* check if a constructor type can be written as a (quantified) Horn clause *)
let is_type_prenex_horn env sigma (t: etypes) : bool =
  let is_ip = is_inductive_prop env sigma in
  (* is the term an implication of inductive props?*)
  (* (as applied to its decomposed arglist) *)
  let is_horn lst = List.for_all is_ip lst in
  (* unfold the term till we reach an inductive prop, the remaining inner term
  must be Horn *)
  let is_prenex_horn lst =
    let inner = List.drop_while (not << is_ip) lst in
    is_horn inner
  in

  let (annotated_args, concl) = decompose_prod sigma t in
  let args = annotated_args |> List.map snd |> List.rev in

  is_ip concl && (is_prenex_horn args)

let is_typed_cons_horn env sigma ((_, cons_ty): econstr * etypes) : bool =
  is_type_prenex_horn env sigma cons_ty  

(* reconstruct a rocq proof term from an internal proof tree *)
(* all branches of the proof must be fully instantiated *)
let proof_tree_to_term 
  (consmap: int -> econstr option) 
  (idtmap: (int, econstr) Hashtbl.t) 
  (tree: Prolog.proof_tree) : econstr = 
  let rec taux = function
    | Term.Var v -> 
      CErrors.user_err (Pp.str "Reconstruction failure: Variable inside substitution mapping")
    | Term.Fun (f, args) ->
      let args' = args |> List.map taux |> List.rev in
      let ft = Hashtbl.find idtmap f in
      EConstr.mkApp (ft, Array.of_list args')
  in
  let rec aux = function
    | Prolog.Leaf (Prolog.IClause (subst, Clause(idx, nv, _, _))) ->
      (* assert List.length subst = nv *)
      let constr = Option.get (consmap idx) in
      let var_args = subst
        |> List.sort_uniq (fun (a, _) (b, _) -> Stdlib.compare a b)
        |> List.map (taux << snd) 
        (* variable assignments shouldn't refer to other vars *)
      in
      EConstr.mkApp (constr, Array.of_list var_args)
    | Prolog.Node (Prolog.IClause (subst, Clause(idx, nv, _, _)), branches) ->
      (* assert List.length subst = nv *)
      let constr = Option.get (consmap idx) in
      let var_args = subst
        |> List.sort_uniq (fun (a, _) (b, _) -> Stdlib.compare a b)
        |> List.map (taux << snd)
        (* variable assignments shouldn't refer to other vars *)
      in
      let proof_args = List.map aux branches in
      let args = Array.of_list (var_args @ proof_args) in
      EConstr.mkApp (constr, args)
    | Prolog.Open _ ->
      CErrors.user_err (Pp.str "Open branches in proof tree")
  in

  aux tree

let horn_proof_search () : unit PV.tactic =
  PV.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in

    let IndType (indf, realargs) =
      match dest_inductive_prop env sigma concl with
      | Some indf -> indf
      | None ->
        let msg = Pp.str "The goal is not an inductive proposition." in
        CErrors.user_err msg
    in
    (* extract all the inductives we have to look at *)
    let reachable_indfs =
      reachable_inductive_families env sigma indf
    in

    (* collect the constructors and their types *)
    (* check that they are well formed wrt our fragment *)
    let cons_w_types = cons_of_families env sigma reachable_indfs in
    let _well_formedness_check =
      match List.find_opt (not << is_typed_cons_horn env sigma) cons_w_types with
      | Some (cstr, cstr_ty) ->
        let base_msg = Pp.str "The reachable set of inductive families is not in the prenex-Horn fragment. Violating constructor: " in
        let ctr_name = Printer.pr_econstr_env env sigma cstr in
        CErrors.user_err (base_msg ++ ctr_name)
      | None -> () (* all constructors can be turned into clauses *)
    in

    (* to each constructor, assign an identifier, and dissociate it and its
    type, turning the type into a clause *)
    let get_or_add_cons, get_cons_by_id = create_cons_map in

    let (cons_clauses, tmap) =
      cons_w_types
      |> List.fold_left begin fun (clauses, tmap) (cstr, cstr_ty) ->
        let cstr_id = get_or_add_cons cstr in
        let cstr_clause, tmap' = clause_of_type env sigma tmap cstr_id cstr_ty in
        cstr_clause :: clauses, tmap'
      end ([], Hashtbl.create 64)
    in

    let goal =
      (* convert as a clause but throw away the wrapper *)
      (* keeping just the head formula *)
      Prolog.dest_hd (fst (clause_of_type env sigma tmap 0 concl))
    in

    match Prolog.dfs cons_clauses goal with
    | None -> 
      let msg = Pp.str "No proof found." in
      CErrors.user_err msg
    | Some proof_tree ->
      (* reconstruct a rocq term from the proof tree *)
      let idtmap = 
        (* flip tmap to get a mapping from integers to terms *)
        let new_map = Hashtbl.create (Hashtbl.length tmap) in
        Hashtbl.iter (fun k v -> Hashtbl.add new_map v k) tmap;
        new_map
      in
      let tt = 
        proof_tree_to_term get_cons_by_id idtmap proof_tree 
      in

      Tactics.exact_check tt
  end

let do_nothing i : unit PV.tactic =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in

    (* normalize and extract the inductive, or raise error *)
    let ((ind, u), t) =
      try pf_apply Tacred.reduce_to_atomic_ind gl concl
      with | UserError _ ->
        let msg = Pp.str "The goal is not an inductive type." in
        CErrors.user_err msg
    in
    (* look at the extraction via inductive families as well *)

    let IndType (indf, realargs) = find_rectype env sigma t in

    let ((indfd, _), _) = dest_ind_family indf in

    let _ = Feedback.msg_info (Pp.str "Inductive: " ++ Pp.str (Names.MutInd.to_string (fst ind)) ++ Pp.str " " ++ Pp.int (snd ind)) in
    let _ = Feedback.msg_info (Pp.str "InductiveFD: " ++ Pp.str (Names.MutInd.to_string (fst indfd)) ++ Pp.str " " ++ Pp.int (snd indfd)) in

    (* realargs *)
    let _ =
      Feedback.msg_info (Pp.str "Real args: ");
      List.iteri
        (fun idx arg ->
          Feedback.msg_info (
            str " Arg "
            ++ str (string_of_int idx)
            ++ str " : "
            ++ Printer.pr_econstr_env env sigma arg
          )
        )
        realargs;
    in

    (* extract constructor names and types *)

    let (constrs, constrs_types) =
      let constrs = Inductiveops.get_constructors env indf in
      let constrs_types = constrs |> Array.map (fun cstr -> type_of_constructor env cstr.cs_cstr) in
      constrs, constrs_types
    in

    (* print constructors and their types *)
    let _ =
      Feedback.msg_info (Pp.str "Constructors: ");
      Array.iter2_i
        (fun idx cstr ctype ->
          Feedback.msg_info (
            str " Cstr "
            ++ str (string_of_int idx)
            ++ str " : "
            ++ Printer.pr_econstr_env env sigma ctype
          )
        )
        constrs constrs_types;
      ()
    in

    let reachable_families = 
      reachable_inductive_families env sigma indf
    in

    (* print list of reachable families *)
    let _ =
      Feedback.msg_info (Pp.str "Reachable families: ");
      List.iteri
        (fun idx indf ->
          let ((indfd, _), _) = dest_ind_family indf in
          Feedback.msg_info (
            str " Inductive family "
            ++ str (string_of_int idx)
            ++ str " : "
            ++ Pp.str (Names.MutInd.to_string (fst indfd))
            ++ Pp.str " #"
            ++ Pp.int (snd indfd)
          )
        )
        reachable_families
    in
    (* do nothing for now *)
    Tacticals.tclIDTAC
  end

(* Wrapper for the trivial tactic *)
let trivial_tac () =
  Auto.gen_auto ~debug:Off None [] None

(* Wrapper for the lia tactic *)
let lia_tac () =
  Micromega_plugin.Coq_micromega.xlia Tacticals.tclIDTAC

(* Hash a goal to create a unique identifier for memoization *)
let hash_goal env sigma concl =
  Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma concl)

(* Clear memoization table - useful between proof attempts *)
let clear_memo_table solved_goals =
  Hashtbl.clear solved_goals

(* Try to get a cached tactic for a goal, or compute and store it *)
let with_memoization compute_tactic solved_goals env sigma concl =
  match solved_goals with
  | None ->
      (* If memoization is disabled, just compute the tactic *)
      compute_tactic ()
  | Some table ->
      (* Use memoization with the provided table *)
      let goal_key = hash_goal env sigma concl in
      try
        Hashtbl.find table goal_key
      with Not_found ->
        let tactic = compute_tactic () in
        Hashtbl.add table goal_key tactic;
        tactic

let rec solve_inductive_goal solved_goals max_depth depth gl =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in

  with_memoization
    (fun () ->
      if depth > max_depth then
        Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "Exceeded maximum search depth")
      else
        match try Some (pf_apply Tacred.reduce_to_atomic_ind gl concl) with _ -> None with
        | Some ((ind, u), t) ->
            let IndType (indf, _realargs) = find_rectype env sigma t in
            let constrs = Inductiveops.get_constructors env indf in

            (* Try each constructor with backtracking *)
            let rec try_constructors = function
              | [] -> Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "No constructor applies")
              | cstr :: rest ->
                  (* Apply constructor then try to solve subgoals recursively *)
                  let try_this_constructor =
                    let c = EConstr.mkConstructU cstr.cs_cstr in
                    Tacticals.tclTHEN
                      (Tactics.eapply c)
                      (Proofview.Goal.enter (solve_subgoals solved_goals max_depth (depth + 1)))
                  in
                  (* If this constructor doesn't work, try the next one *)
                  Tacticals.tclORELSE try_this_constructor (try_constructors rest)
            in
            try_constructors (Array.to_list constrs)

        | None ->
            (* For non-inductive goals, try tactics that might solve them directly *)
            Tacticals.tclFIRST [
              Tactics.reflexivity;
              Tactics.assumption;
              trivial_tac ();
              lia_tac ();
              Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "Not an inductive goal and no direct tactic applies")
            ]
    )
    solved_goals env sigma concl

(* Try to solve all subgoals recursively with backtracking *)
and solve_subgoals solved_goals max_depth depth gl =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in

  with_memoization
    (fun () ->
      Tacticals.tclPROGRESS (
        Tacticals.tclFIRST [
          solve_inductive_goal solved_goals max_depth depth gl;
          Tactics.reflexivity;
          Tactics.assumption;
          Tactics.simpl_in_concl;
          trivial_tac ();
          lia_tac ();
          (* Equality.discriminate; *)
        ]
      )
    )
    solved_goals env sigma concl

(* Iterative deepening search to find the shallowest proof *)
let iterative_deepening_search solved_goals max_depth gl =
  let rec try_with_depth d =
    if d > max_depth then
      Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "Exceeded maximum search depth")
    else
      Tacticals.tclORELSE
        (solve_inductive_goal solved_goals d 0 gl)
        (try_with_depth (d + 1))
  in
  try_with_depth 1

let chc_auto ?(max_depth=20) ?(use_deepening=false) ?(use_memo=true) () =
  (* Memoization table to avoid redundant work *)
  let solved_goals = if use_memo then Some (Hashtbl.create 50) else None in

  Proofview.Goal.enter begin fun gl ->
    if use_deepening then
      iterative_deepening_search solved_goals max_depth gl
    else
      solve_inductive_goal solved_goals max_depth 0 gl
  end |> Tacticals.tclCOMPLETE
