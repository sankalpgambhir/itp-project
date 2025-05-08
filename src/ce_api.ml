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

module PV = Proofview

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

    let _ = Feedback.msg_info (Pp.str "Inductive: " ++ Pp.str (Names.MutInd.to_string (fst ind))) in
    let _ = Feedback.msg_info (Pp.str "InductiveFD: " ++ Pp.str (Names.MutInd.to_string (fst indfd))) in

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

    (* what does a forall look like *)
    (* destruct a constructor type into args and res *)
    let (binder, args, res) = 
      try destProd sigma constrs_types.(1)
      with | UserError _ -> 
        let msg = Pp.str "The constructor type is not a product." in
        CErrors.user_err msg
    in

    (* print the binder, args and res *)
    let _ = 
      Feedback.msg_info (Pp.str "Binder: ");
      (* Feedback.msg_info ( env sigma binder); *)
      Feedback.msg_info (Pp.str "Args: ");
      (* List.iteri *)
      (fun arg ->
        Feedback.msg_info (
          str " Arg "
          (* ++ str (string_of_int idx) *)
          ++ str " : "
          ++ Printer.pr_econstr_env env sigma arg
        )
      ) args;
      Feedback.msg_info (Pp.str "Res: ");
      Feedback.msg_info (Printer.pr_econstr_env env sigma res)
    in

    (* do nothing for now *)
    Tacticals.tclIDTAC
  end

(* Tactic: oltauto with certification*)