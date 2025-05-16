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
