
(* 
    Prolog-like proof search engine
*)

open Coutils

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

let dest_id (Clause (id, _, _, _)) = id

let dest_hd (Clause (_, _, f, _)) = f
  
(* fact database *)
type db = clause list

type clause_set = clause list

type subst = (var * term) list

type iclause =
  | IClause of subst * clause

type proof_tree =
  | Leaf of iclause 
  (* Leaf of fact *)
  (* can only be produced as the instantiation of a fact clause in the problem *)
  (* the problem is unsolvable if it has no fact clauses, as branches must stay open *)
  | Node of iclause * proof_tree list
  (* Node of reduced_clause * arguments_for_body *) 
  (* invariant :: reduced_clause has empty body (is a proven atomic fact if its branches are closed) *)
  (* note: some variables may not be fully instantiated if the proof is constructor bottom up *)
  (* this corresponds to proofs of universally quantified atoms *)
  | Open of formula 
  (* Open of goal *)


(* pretty print a term *)
let rec string_of_term (t: term) : string =
  match t with
  | Var v -> Printf.sprintf "X%d" v
  | Fun (f, args) -> 
    let args_str = String.concat ", " (List.map string_of_term args) in
    Printf.sprintf "F%d(%s)" f args_str

(* pretty print a formula *)
let string_of_formula (f: formula) : string =
  match f with
  | Atom (Predicate p, ts) -> 
    let ts_str = String.concat ", " (List.map string_of_term ts) in
    Printf.sprintf "P%d(%s)" p ts_str

(* pretty print a clause *)
let string_of_clause (c: clause) : string =
  match c with
  | Clause (id, nv, head, body) -> 
    let body_str = String.concat " /\\ " (List.map string_of_formula body) in
    Printf.sprintf "C%d: %s :- %s" id (string_of_formula head) body_str

(* print proof trees *)
let rec print_proof_tree (pt: proof_tree) : string =
  match pt with
  | Leaf (IClause (s, c)) -> 
    Printf.sprintf "Leaf: %s\n" (string_of_clause c)
  | Node (IClause (s, c), proofs) -> 
    Printf.sprintf "Node: %s\n%s" (string_of_clause c) ((List.map print_proof_tree proofs) |> String.concat "")
  | Open f -> 
    Printf.sprintf "Open: %s\n" (string_of_formula f)


  
let empty_subst = []

(* Check if `a` maps to `b` under `sub` *)
let substs sub a b = List.assoc_opt a sub = Some b

(* add a substitution to a substitution list *)
let subst_add sub a b = (a, b) :: List.remove_assoc a sub

(* add a substitution knowing it is safe to add, i.e. a is not in the list *)
let subst_add_unsafe sub a b = (a, b) :: sub

(* apply a substitution to a term *)
let rec apply_subst sub t =
  match t with
  | Var v -> 
    List.assoc_opt v sub
      |> Option.cata identity t
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
    | Var v, Fun (f, args) ->
      if substs s v (Fun (f, args)) then Some s
      else Some (subst_add_unsafe s v (Fun (f, args)))
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

let match_and_resolve (clause: clause) (goal: formula): (subst * formula list) option =
  match clause with
  | Clause (id, nv, head, body) ->
    let sub_opt = matches head goal in
    match sub_opt with
    | None -> None
    | Some s ->
      (* unified body atoms as new goals *)
      let body' = body |> List.map (apply_subst_formula s) in
      Some (s, body')

module Formula_set = Set.Make(
  struct type t = formula

  let rec tcmp a b =
    match a, b with
    | Var v1, Var v2 -> compare v1 v2
    | Var v1, _ -> -1
    | _, Var v2 -> 1
    | Fun (f1, args1), Fun (f2, args2) ->
      let cmp = compare f1 f2 in
      if cmp = 0 then
        List.compare tcmp args1 args2
      else cmp
      
  let compare a b =
    match a, b with
    | Atom (p1, ts1), Atom (p2, ts2) ->
      let cmp = compare p1 p2 in
      if cmp = 0 then
        List.compare tcmp ts1 ts2
      else cmp
end)

let dfs (clauses: clause_set) (goal: formula) : proof_tree option =
  (* memoize *)
  let proof_cache = Hashtbl.create 32 in
  (* helpers *)
  let facts = List.filter is_fact clauses in
  (* actual dfs *)
  (*
    invariant: since we move top-down, 
    the goal argument is always fully instantiated
  *)
  let rec dfs_step visited (goal: formula) : proof_tree option =
    if Hashtbl.mem proof_cache goal then
      (* already proved or disproved *)
      Hashtbl.find proof_cache goal
    else if Formula_set.mem goal visited then
      (* this is a non-terminating branch *)
      (* backtrack *)
      (* it is safe (and recommended) to check the cache and visited in this order *)
      (* a proof for this goal may have been discovered in another otherwise failed branch *)
      None
    else 
      (* attempt to close early with a fact *)
      let fact_opt = facts 
                      |> List.find_map (function
                        | Clause (idx, nv, hd, _) -> 
                          matches hd goal 
                            |> Option.map (fun s -> 
                              IClause (s, Clause (idx, nv, goal, []))
                            )
                      ) 
      in
      match fact_opt with
      | Some f -> 
        let proof = Some (Leaf f) in
        Hashtbl.add proof_cache goal proof;
        proof
      | None ->
        (* attempt to branch and resolve *)
        let visited' = Formula_set.add goal visited in 
        clauses
          |> List.find_map (fun c ->
            (* 
              first clause that not only matches, 
              but has resolvable branches too
            *) 
            match_and_resolve c goal
            (* can we resolve each of the branches? *)
            |> Option.map ( fun (s, bs) ->
              let inner = 
                bs 
                  |> List.rev
                  |> List.fold_left (fun (failed, acc) b ->
                    if failed then 
                      (* don't try the remaining *)
                      (failed, acc)
                    else
                      (* keep going *)
                      match dfs_step visited' b with
                      | None -> (true, acc)
                      | Some proof -> 
                        (false, proof :: acc)                    
                  ) (false, [])
              in
              match inner with
              | (true, _) -> None
              | (false, proofs) -> Some (c, s, proofs)
            )
            |> Option.flatten
          )
          |> Option.map (fun (c, s, proofs) ->
              (* all branches were closed, wrap it in a node *)
              let Clause (id, nv, _, _) = c in
              let top = Clause (id, nv, goal, []) in
              let proof = Node (IClause (s, top), proofs) in
              (* add to the cache *)
              Hashtbl.add proof_cache goal (Some proof);
              proof
            )
  in
  dfs_step Formula_set.empty goal
