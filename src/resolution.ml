
open Coutils
open Term

(* Clause with lists of positive and negative literals *)
type clause =
  | Clause of formula list * formula list

module Clause = struct 
  type t = clause
  
  let is_fact = function
    | Clause ([], [Atom _]) -> true
    | _ -> false

  let is_empty = function
    | Clause ([], []) -> true
    | _ -> false

  let pos = function
    | Clause (pos, _) -> pos

  let neg = function
    | Clause (_, neg) -> neg
end

