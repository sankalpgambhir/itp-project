
(* 
    Prolog-like proof search engine
*)

open Coutils

(*
  TODO: REWRITE WRT CHANGED CLAUSES

  Every clause should carry an integer ID, and we cannot just reduce clauses
  dynamically without care. We need to be sure that the ID is preserved,
  alongside the instantiations that led to the reduction.
*)

(* Formula definitions *)

(* term algebra T(F, X) *)
type var = int

type term = 
  | Var of var (* a var is implicitly universally quantified in clauses *)
  | Fun of int * term list

let is_var = function
  | Var _ -> true
  | _ -> false

let is_fun = function
  | Fun _ -> true
  | _ -> false

let is_const = function
  | Fun (_, []) -> true
  | _ -> false

let dest_fun = function
  | Fun (f, args) -> f, args
  | _ -> failwith "dest_fun: not a function"


(* simple predicate logic atoms *)
type predicate = 
  | Predicate of int

type formula =
  | Atom of predicate * term list

type clause = 
  (* 
    id, number of variables, head, body
    
    head :- body1 /\ body2 /\ ... 
  *)
  | Clause of int * int * formula * formula list 

let is_fact = function
  | Clause (_, _, Atom _, []) -> true
  | _ -> false

let clause_of f = Clause (0, 0, f, [])

(* fact database *)
type db = clause list

type clause_set = clause list

type subst = (var * term) list

type iclause =
  | IClause of subst * clause

let empty_subst = []

(* Check if `a` maps to `b` under `sub` *)
let substs sub a b = List.assoc a sub = b

(* add a substitution to a substitution list *)
let subst_add sub a b = (a, b) :: List.remove_assoc a sub

(* add a substitution knowing it is safe to add, i.e. a is not in the list *)
let subst_add_unsafe sub a b = (a, b) :: sub

(* apply a substitution to a term *)
let rec apply_subst sub t =
  match t with
  | Var v -> 
    (try List.assoc v sub with Not_found -> t)
  | Fun (f, args) -> 
    Fun (f, List.map (apply_subst sub) args)

(* apply a substitution to a formula *)
let apply_subst_formula sub f =
  match f with
  | Atom (p, ts) -> 
    Atom (p, List.map (apply_subst sub) ts)

(* apply a substitution to a clause *)
let apply_subst_clause sub (Clause (id, nv, head, body)) =
  Clause (id, nv, apply_subst_formula sub head, List.map (apply_subst_formula sub) body)

(* returns a minimal substitution if t1 can be matched against t2, by
instantiating variables in t1 alone, None if no matches *)
let rec term_matches (partial: subst option) (t1: term) (t2: term) : subst option =
  match partial with
  | None -> None
  | Some s ->
    match t1, t2 with
    | Var v1, Var v2 -> 
      if v1 = v2 then Some s
      else if substs s v1 (Var v2) then Some s
      else Some (subst_add_unsafe s v1 (Var v2))

    | Fun (f1, args1), Fun (f2, args2) when f1 = f2 && List.length args1 = List.length args2 ->
      List.fold_left2 term_matches (Some s) args1 args2

    | _ -> None 

(* returns a minimal substitution if f1 can be matched against f2, by
instantiating variables in f1 alone, None if no matches *)
let matches (f1: formula) (f2: formula) : subst option = 
  match f1, f2 with
  | Atom (p, ts), Atom (q, ss) when p = q && List.compare_lengths ts ss == 0 ->
      List.fold_left2 term_matches (Some empty_subst) ts ss
  | _ -> None

let match_and_resolve (clause: clause) (goal: formula): formula list option =
  match clause with
  | Clause (id, nv, head, body) ->
    let sub_opt = matches head goal in
    match sub_opt with
    | None -> None
    | Some s ->
      (* unified body atoms as new goals *)
      let body' = body |> List.map (apply_subst_formula s) in
      Some body'

(* dfs *)
let dfs (clauses: clause_set) (goal: formula) : clause list option =
  (* prevent loops *)
  let visited_tbl = Hashtbl.create 32 in
  let visited_or_visit g = 
    if Hashtbl.mem visited_tbl g then
      true
    else begin
      Hashtbl.add visited_tbl g ();
      false
    end
  in
  (* run dfs with backtracking to reduce a list of goals to a fact db *)
  (* returns the list of clauses resolved against (in reverse order) *)
  let rec dfs_step cs db goals acc =
    match goals with
    | [] -> Some acc (* no more goals, steps complete *)
    | g :: gs -> 
      if visited_or_visit g then 
        (* this is a non-terminating branch *)
        (* backtrack *)
        None
      else if List.mem g db then
        (* this is a fact, discharge goal *)
        dfs_step cs db gs (clause_of g :: acc)
      else
        (* resolve against clauses that match, exploring each branch while
        backtracking *)
        (* resolve this goal *)
        (* intentionally reuses the full clause set *)
        let res = explore cs db g gs acc in
        match res with
        | None -> 
          (* cannot prove this goal, fail *)
          None
        | Some path ->
          (* found a path, continue with other goals *)
          dfs_step cs db gs (path @ acc)
  (* explore the branches that reduce a given goal, backtracking and resuming
  dfs as necessary*)
  and explore cs db g gs acc =
    match cs with
    | [] -> None
    | c :: cs' ->
      match match_and_resolve c g with
      | None -> 
        (* no match, continue exploring *)
        explore cs' db g gs acc
      | Some new_goals ->
        (* add the new goals to the list of goals, restart dfs *)
        let branch = dfs_step cs db (new_goals @ gs) (c :: acc) in
        match branch with
        | Some _ -> branch
        | None -> 
          (* backtrack, continue exploring *)
          explore cs' db g gs acc
  in
  let opt_dest_fact = function 
    | Clause (_, _, f, []) -> Some f 
    | _ -> None
  in
  let db = List.filter_map opt_dest_fact clauses in
  let cs = List.filter (not << is_fact) clauses in 
  let dfs_res = dfs_step cs db [goal] [] in
    Option.map List.rev dfs_res

(* API *)

(* given a set of clauses and a goal, produce a list of steps that can be sequentially applied  *)
let query (clauses: clause_set) (goal: formula) : clause list option =
  dfs clauses goal