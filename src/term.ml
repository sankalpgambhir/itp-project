
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

type literal =
  | Pos of formula
  | Neg of formula

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

(* pretty print a literal *)
let string_of_literal (l: literal) : string =
  match l with
  | Pos f -> Printf.sprintf "%s" (string_of_formula f)
  | Neg f -> Printf.sprintf "¬ %s" (string_of_formula f)


(* substitutions *)

type subst = (var * term) list

let empty_subst = []

(* Check if `a` maps to `b` under `sub` *)
let substs sub a b = List.assoc_opt a sub = Some b

(* add a substitution to a substitution list *)
let subst_add sub a b = (a, b) :: List.remove_assoc a sub

(* add a substitution knowing it is safe to add, i.e. a is not in the list *)
let subst_add_unsafe sub a b = (a, b) :: sub

(* lookup a variable in a substitution *)
let subst_lookup sub a = List.assoc_opt a sub

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

let rec occurs (v: var) (t: term) : bool =
  match t with
  | Var v' -> v = v'
  | Fun (_, args) -> List.exists (occurs v) args

(* returns a minimal substitution if t1 can be matched against t2, by
instantiating variables in t1 alone, None if no matches *)
let rec term_matches (partial: subst option) (t1: term) (t2: term) : subst option =
  match partial with
  | None -> None
  | Some s ->
    let u = apply_subst s t1 in
    let v = apply_subst s t2 in
    match u, v with
    | _ when u = v -> Some s
    | Var v1, Var v2 when v1 = v2 -> Some s
    | Var v, t when not (occurs v t) -> Some (subst_add_unsafe s v t)
    | Fun (f1, args1), Fun (f2, args2) when f1 = f2 && List.compare_lengths args1 args2 = 0 ->
      List.fold_left2 term_matches (Some s) args1 args2
    | _ -> None

(* returns a minimal substitution if f1 can be matched against f2, by
instantiating variables in f1 alone, None if no matches *)
let formula_matches (f1: formula) (f2: formula) : subst option = 
  match f1, f2 with
  | Atom (p, ts), Atom (q, ss) when p = q && List.compare_lengths ts ss = 0 ->
      List.fold_left2 term_matches (Some empty_subst) ts ss
  | _ -> None

(* left biased term unification; will always attempt to instantiate the left when both sides are variables *)
let rec term_unifies (partial: subst option) (t1: term) (t2: term): subst option =
  match partial with
  | None -> None
  | Some s ->
    let u = apply_subst s t1 in
    let v = apply_subst s t2 in
    match u, v with
    | _ when u = v -> Some s
    | Var v1, Var v2 when v1 = v2 -> Some s
    | Var v, t when not (occurs v t) -> Some (subst_add_unsafe s v t)
    | t, Var v when not (occurs v t) -> Some (subst_add_unsafe s v t)
    | Fun (f1, args1), Fun (f2, args2) when f1 = f2 && List.compare_lengths args1 args2 = 0 ->
      List.fold_left2 term_unifies (Some s) args1 args2
    | _ -> None

(* left biased formula unification; will always attempt to instantiate the left when both sides are variables *)
let formula_unifies (f1: formula) (f2: formula) : subst option = 
  match f1, f2 with
  | Atom (p, ts), Atom (q, ss) when p = q && List.compare_lengths ts ss = 0 ->
      List.fold_left2 term_unifies (Some empty_subst) ts ss
  | _ -> None

let rec tcompare a b =
  match a, b with
  | Var v1, Var v2 -> compare v1 v2
  | Var v1, _ -> -1
  | _, Var v2 -> 1
  | Fun (f1, args1), Fun (f2, args2) ->
    let cmp = compare f1 f2 in
    if cmp = 0 then
      List.compare tcompare args1 args2
    else cmp
    
let fcompare a b =
  match a, b with
  | Atom (p1, ts1), Atom (p2, ts2) ->
    let cmp = compare p1 p2 in
    if cmp = 0 then
      List.compare tcompare ts1 ts2
    else cmp

module Formula_set = Set.Make(
  struct type t = formula

  let compare = fcompare
end)

module Literal_set = Set.Make(
  struct type t = literal

  let compare a b =
    match a, b with
    | Pos _, Neg _ -> -1
    | Neg _, Pos _ -> 1
    | Pos f1, Pos f2 -> fcompare f1 f2
    | Neg f1, Neg f2 -> fcompare f1 f2
end)

(* On interpreted terms and predicates *)

let interpreted_predicates : (string * int) list =
  [
    "le";
    "lt";
    "ge";
    "gt";
  ]
  |> List.mapi (fun i s -> s, -i - 1)

let interpreted_functions : (string * int) list =
  [
    "0";
    "S";
  ]
  |> List.mapi (fun i s -> s, -i - 1)
