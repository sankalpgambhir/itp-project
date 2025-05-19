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
let rec constr_to_term env sigma vmap (tmap: constrtbl) (t: econstr) : Prolog.term * constrtbl =
  (* we assume a first-order abstraction over the terms *)
  (* functions are not checked or expanded further *)
  (* arguments are transformed recursively *)
  let func, args = decompose_app sigma t in
  let fid = hashtbl_get_or_inc tmap func in
  let args_list = Array.to_list args in
  let args', tmap' = constr_list_to_term env sigma vmap tmap args_list in
  Prolog.Fun (fid, args'), tmap'
and constr_list_to_term env sigma vmap (tmap: constrtbl) (ts: econstr list) : Prolog.term list * constrtbl =
  let args', tmap' =
    List.fold_right (fun t (acc, tmap) -> 
      let (t', tmap') = constr_to_term env sigma vmap tmap t in
      (t' :: acc, tmap')
    ) ts ([], tmap)  
  in
  args', tmap'

(* create a mapping from terms to internal formulas *)
let constr_to_formula env sigma vmap (tmap: constrtbl) (t: econstr) : Prolog.formula * constrtbl =
  (* requires: the term is a prop possibly applied to something *)
  let func, args = decompose_app sigma t in
  let fid = hashtbl_get_or_inc tmap func in
  let args_list = Array.to_list args in
  let args', tmap' = constr_list_to_term env sigma vmap tmap args_list in
  Prolog.Atom ((Prolog.Predicate fid), args'), tmap'

(* construct an internal wrapped clause from a constructor type *)
let clause_of_type env sigma (cstr_id: int) (ty: etypes) : Prolog.clause =
  (* decompose the product type *)
  (* and separate the term arguments, i.e. non-props *)
  let (annotated_args, concl) = decompose_prod sigma ty in

  (* 
    each annotated argument is a pair of (name, relevance) 
    
    name can be an actual `Name id` or `Anonymous`.
    
    TODO: unclear how to handle anonymous names in our context. Does a term
    parameter for an inductive prop constructor matter if you do not name and
    use it? Given that all types are known to be non-empty.

    The relevance is a wrapped `Sorts.relevance`, which tracks whether the
    parameter is proof relevant. This is not *us*-relevant, at least.
  *)

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

  (* all variables are local, and the formula is prenex
    so just name the variables 0..n-1
  *)
  let vmap, prop_args =
    (* both of these are tail rec (modulo cons) *)
    (* trying to do them both together is not necessarily great *)
    let ann_vs = List.take_while (is_inductive_prop env sigma << snd) annotated_args in
    let vs = ann_vs
      |> List.map (binder_name << fst)
      |> List.map (function
        | Name.Name id -> id
        | Name.Anonymous -> failwith "TODO: Anonymous name in clause_of_type"
      )
    in
    let prop_args = annotated_args
      |> List.drop_while (is_inductive_prop env sigma << snd)
      |> List.map snd 
      (* discarding names is fine if the inner terms are not dependent on us (shouldn't be) *)
    in
    List.map_i (fun idx x -> x, idx) 0 vs, prop_args
  in

  let empty_tmap = Hashtbl.create 32 in
  let to_form = constr_to_formula env sigma vmap empty_tmap in

  let clause_body = List.map to_form prop_args in
  let clause_head = to_form concl in
  
  Clause (cstr_id, clause_head, clause_body)

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
  let args = List.map snd annotated_args in

  is_ip concl && (is_prenex_horn args)

let is_typed_cons_horn env sigma ((_, cons_ty): econstr * etypes) : bool =
  is_type_prenex_horn env sigma cons_ty  

let horn_proof_search : unit PV.tactic =
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

    let cons_clauses =
      cons_w_types
      |> List.map begin fun (cstr, cstr_ty) ->
        let cstr_id = get_or_add_cons cstr in
        let cstr_clause = clause_of_type env sigma cstr_id cstr_ty in
        cstr_clause
      end
    in
    
    Tacticals.tclIDTAC
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

let rec solve_inductive_goal max_depth depth gl =
  if depth > max_depth then
    Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "Exceeded maximum search depth")
  else
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
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
                  (Tactics.apply c)
                  (Proofview.Goal.enter (solve_subgoals max_depth (depth + 1)))
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
          Tacticals.tclFAIL ~info:Exninfo.null (Pp.str "Not an inductive goal and no direct tactic applies")
        ]

(* Try to solve all subgoals recursively with backtracking *)
and solve_subgoals max_depth depth gl =
  Tacticals.tclPROGRESS (
    Tacticals.tclFIRST [
      solve_inductive_goal max_depth depth gl;
      Tactics.reflexivity;
      Tactics.assumption;
      trivial_tac ();
    ]
  )
let chc_auto ?(max_depth=20) () =
  Tacticals.tclCOMPLETE (
    Proofview.Goal.enter (solve_inductive_goal max_depth 0)
  )
