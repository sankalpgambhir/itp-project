
(* open Z3

let new_solver () = 
  let ctx = Z3.mk_context [] in
  let solver = Solver.mk_solver ctx None in
  ctx, solver

let interpreted_to_z3 =
  [
    "le", begin fun (ctx, es) ->
      match es with
      | [e1; e2] ->
        let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in 
        let ll = Z3.Arithmetic.mk_le ctx e1 e2 in
        let nat1 = Z3.Arithmetic.mk_ge ctx e1 zero in
        let nat2 = Z3.Arithmetic.mk_ge ctx e2 zero in
        Z3.Boolean.mk_and ctx [ll; nat1; nat2]
      | _ -> failwith "interpreted_to_z3: expected 2 arguments for 'le'"
    end;
    "lt", begin fun (ctx, es) ->
      match es with
      | [e1; e2] ->
        let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in 
        let ll = Z3.Arithmetic.mk_lt ctx e1 e2 in
        let nat1 = Z3.Arithmetic.mk_ge ctx e1 zero in
        let nat2 = Z3.Arithmetic.mk_ge ctx e2 zero in
        Z3.Boolean.mk_and ctx [ll; nat1; nat2]
      | _ -> failwith "interpreted_to_z3: expected 2 arguments for 'lt'" 
    end;
    "ge", begin fun (ctx, es) ->
      match es with
      | [e1; e2] ->
        let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in 
        let ll = Z3.Arithmetic.mk_ge ctx e1 e2 in
        let nat1 = Z3.Arithmetic.mk_ge ctx e1 zero in
        let nat2 = Z3.Arithmetic.mk_ge ctx e2 zero in
        Z3.Boolean.mk_and ctx [ll; nat1; nat2]
      | _ -> failwith "interpreted_to_z3: expected 2 arguments for 'ge'"
    end;
    "gt", begin fun (ctx, es) ->
      match es with
      | [e1; e2] ->
        let zero = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in 
        let ll = Z3.Arithmetic.mk_gt ctx e1 e2 in
        let nat1 = Z3.Arithmetic.mk_ge ctx e1 zero in
        let nat2 = Z3.Arithmetic.mk_ge ctx e2 zero in
        Z3.Boolean.mk_and ctx [ll; nat1; nat2]
      | _ -> failwith "interpreted_to_z3: expected 2 arguments for 'gt'"
    end;
  ]

let term_int_value (t: Term.term) : int =
  let s = List.assoc "S"Term.interpreted_functions in
  let zero = List.assoc "0" Term.interpreted_functions in
  let rec aux t value =
    match t with
    | Term.Fun (id, args) when id = s ->
      let inner = List.hd args in
      aux inner (value + 1)
    | Term.Fun (id, []) when id = zero ->
      value
    | _ -> failwith "term_int_value: expected a term of the form S(...S(0))"
    in
  aux t 0

let interpreted_as_smt (ctx: Z3.context) (f: Term.formula) : Expr.expr =
  match f with
    | Term.Atom (Term.Predicate p, ts) ->
      let name = List.find_map (fun (s, n) -> if n = p then Some s else None) Term.interpreted_predicates  |> Option.get in
      let args = ts |> List.map (term_int_value) |> List.map (Z3.Arithmetic.Integer.mk_numeral_i ctx) in
      let eval = List.assoc name interpreted_to_z3 in
      eval (ctx, args)

let is_unsat (fs: Term.formula list): bool =
  let ctx, solver = new_solver () in
  let es = List.map (interpreted_as_smt ctx) fs in
  Solver.add solver es;
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> true
  | Solver.SATISFIABLE | Solver.UNKNOWN -> false
 *)
