
(* 
    Prolog-like proof search engine
*)

open Coutils
open Term

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

(* apply a substitution to a clause *)
let apply_subst_clause sub (Clause (id, nv, head, body)) =
  Clause (id, nv, apply_subst_formula sub head, List.map (apply_subst_formula sub) body)

let match_and_resolve (clause: clause) (goal: formula): (subst * formula list) option =
  match clause with
  | Clause (id, nv, head, body) ->
    let sub_opt = formula_matches head goal in
    match sub_opt with
    | None -> None
    | Some s ->
      (* unified body atoms as new goals *)
      let body' = body |> List.map (apply_subst_formula s) in
      Some (s, body')

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
                          formula_matches hd goal 
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
