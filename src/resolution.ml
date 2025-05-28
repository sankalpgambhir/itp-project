
open Coutils
open Term

(* Clause with lists of positive and negative literals *)
type clause =
  | Clause of int * int * formula list * formula list

module Clause = struct 
  type t = clause
  
  let is_fact = function
    | Clause (_, _,  [], [Atom _]) -> true
    | _ -> false

  let is_empty = function
    | Clause (_, _, [], []) -> true
    | _ -> false

  let pos = function
    | Clause (_, _, pos, _) -> pos

  let neg = function
    | Clause (_, _, _, neg) -> neg

  let hd = function
    | Clause (_, _, pos, _) when pos <> [] -> List.hd pos
    | _ -> failwith "Clause.hd: no head"
end

(* printing *)
let string_of_clause = function
  | Clause (_, _, pos, neg) ->
    let pos = List.map string_of_literal (List.map (fun x -> Pos x) pos) in
    let neg = List.map string_of_literal (List.map (fun x -> Neg x) neg) in
    String.concat " ∨ " (pos @ neg)

(* proof tree *)
type proof_tree =
  (* clause arising from problem, instantiated *)
  | End
  | Axiom of clause * subst
  (* resolution (left biased) 
      f, sub, p1, p2
      where 
      - f is the resolution pivot
      - sub is the substitution applied to p1
      - p1.clause is the proof tree for the first clause
      - p1 must contain ¬f
      - p2 is the proof tree for the second clause
      - p2.clause must contain f
  *)
  | Resolution of formula * proof_tree * proof_tree

let string_of_proof_tree pp =
  let indent = List.map (fun s -> "  " ^ s) in
  let rec stringify pp =
    match pp with
    | End -> ["End"]
    | Axiom (c, sub) -> 
      let Clause (id, nv, pos, neg) = c in
      let subs = 
        sub
        |> List.filter (function (a, _) -> a >= 0)
        |> List.sort_uniq (fun (a, _) (b, _) -> compare a b)
        |> List.take nv
        |> List.map (string_of_term << snd)
        |> String.concat ", "
      in
      [Printf.sprintf "Axiom: %s subst %s" (string_of_clause c) subs]
    | Resolution (f, p1, p2) ->
      ("Resolution: " ^ (string_of_formula f)) ::
        (indent (stringify p1)) @
        (indent (stringify p2))
  in
  String.concat "\n" (stringify pp)

let fresh_var_or_get =
  (* lookup a variable mapping to a fresh one *)
  (* if not found, create one *)
  let counter = ref (-1) in
  let next = fun () ->
    let v = !counter in
    counter := !counter - 1;
    !counter
  in
  let tbl = Hashtbl.create 32 in
  let lookup v =
    try Hashtbl.find tbl v
    with Not_found ->
      let new_v = next () in
      Hashtbl.add tbl v new_v;
      Hashtbl.add tbl new_v new_v;
      new_v
    in
  lookup

let rec freshen_vars = function
  | Var v -> Var (fresh_var_or_get v)
  | Fun (f, args) -> Fun (f, List.map freshen_vars args)

let rec apply_subst_term_freshen sub = function
  | Var v ->
    (match List.assoc_opt v sub with
     | Some t -> freshen_vars t
     | None -> Var (fresh_var_or_get v))
  | Fun (f, args) ->
    Fun (f, List.map (apply_subst_term_freshen sub) args)

let apply_subst_freshen sub = function
  | Atom (p, args) ->
    Atom (p, List.map (fun t -> apply_subst_term_freshen sub t) args)

(* instantiate any variable substitutions of s1 if they have been instantiated in s2 *)
let refine_subst (s1: subst) (s2: subst) : subst =
  let s1' = s1
  |> List.map begin function
      | (v, Var v') ->
        (match List.assoc_opt v' s2 with
        | Some t -> (v, t)  (* use the term from s2 *)
        | None -> (v, Var v'))  (* keep the original variable if not found in s2 *)
      | (v, t) -> (v, t)  (* keep non-variable terms as is *)
    end
  in
  s1' @ s2

let refine_subst_freshen (s: subst) : subst =
  s
  |> List.map begin function
      | (v, Var v') -> (v, Var (fresh_var_or_get v'))
      | (v, t) -> (v, freshen_vars t) 
    end

type clause_db = (int, (clause list)) Hashtbl.t

let construct_db (cls: clause list) : clause_db =
  let tbl = Hashtbl.create 64 in
  let head_weight (f: formula): int = 
    let rec term_weight (t: term): int =
      match t with
      | Var _ -> 3
      | Fun (_, args) -> 1 + List.fold_left (fun acc a -> acc + term_weight a) 0 args
    in
    match f with
    | Atom (_, args) -> List.fold_left (fun acc a -> acc + term_weight a) 0 args
  in
  let cmp c1 c2 = 
    head_weight (Clause.hd c1) - head_weight (Clause.hd c2)
  in
  cls
  |> List.iter begin function 
      | Clause (id, _, pos, neg) ->
        (* store clauses by their head literal *)
        let headid = match pos with
          | [] -> failwith "construct_db: clause has no positive literals"
          | Atom (Predicate id, _) :: _ -> id
        in
        let existing = Hashtbl.find_opt tbl headid |> Option.default [] in
        Hashtbl.replace tbl headid (Clause (id, 0, pos, neg) :: existing)
    end;
  (* sort the clauses by head weight *)
  Hashtbl.filter_map_inplace (fun _ v -> Some (List.sort cmp v)) tbl;
  tbl

let find_matching (cls: clause_db) (goal: formula) : (clause * subst) option =
  (* find a clause that matches the goal *)
  let pred_id = 
    match goal with
    | Atom (Predicate id, _) -> id
  in
  Hashtbl.find_opt cls pred_id
  |> Option.default []
  |> List.find_map begin fun c ->
      match formula_matches (Clause.hd c) goal with
      | None -> None
      | Some subst ->
        Some (c, subst)
    end

let find_unifier (cls: clause_db) (goal: formula) : (clause * subst) option =
  (* find a clause that unifies with the goal *)
  let pred_id = 
    match goal with
    | Atom (Predicate id, _) -> id
  in
  Hashtbl.find_opt cls pred_id
  |> Option.default []
  |> List.find_map begin fun c ->
      match formula_unifies (Clause.hd c) goal with
      | None -> None
      | Some subst ->
        Some (c, subst)
    end

(* resolution proof search *)
let resolution_proof (cls: clause list) (goal: formula) : proof_tree option =
  (* invariant: goal is always a set of positive literals *)
  (* invariant: db clauses are always definite Horn *)
  let rec aux (db: clause_db) (goal: formula list): (subst * proof_tree) option =
    (* if goal is empty, we have a proof *)
    match goal with
    | [] -> 
      Some (empty_subst, End)
    | gl :: rest ->
      (* try to resolve the first goal by matching *)
      (* if that fails, try to unify to resolve evars *)
      find_matching db gl 
        |> or_else (fun () -> find_unifier db gl)
        |> Option.map begin fun (c, subst) ->
            let rest' = List.map (apply_subst_freshen subst) rest in
            let new_goals = List.map (apply_subst_freshen subst) (Clause.neg c) in
            (* order is important, matches the stack behaviour of `Tactics.apply` *)
            let next = new_goals @ rest' in
            let inner_proof = aux db next in
            match inner_proof with
            | None -> None
            | Some (inner_subst, inner_proof) ->
              let subst' = refine_subst subst inner_subst in
              Some (subst', Resolution (gl, Axiom (c, subst'), inner_proof))
          end
        |> Option.flatten
      in
  let db = construct_db cls in
  aux db [goal]
    |> Option.map snd

