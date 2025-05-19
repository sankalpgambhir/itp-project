
(* utils *)

(* function composition *)
let (<<) f g x = f(g(x))

let identity x = x

(* create side-effecting assoc list accessors *)
(* compiler complains if this is polymorphic *)
(* I don't want to mvoe this into a module and instantiate that *)
(* so it is specialized to Econstr till I have a better solution*)
let create_cons_map =
  let mmap = ref ([]: (EConstr.t * int) list)
  and ccounter = ref 0 in
  let add k = 
    mmap := (k, !ccounter)::!mmap;
    ccounter := !ccounter + 1;
    !ccounter - 1
  in
  let get k = 
    List.assoc_opt k !mmap
      (* else add *)
      |> Option.cata identity (add k)
  in
  let get_rev v =
    List.find_opt (fun (_, v') -> v = v') !mmap
      |> Option.map fst
  in
  (get, get_rev)

type constrtbl = (EConstr.t, int) Hashtbl.t

let hashtbl_get_or_inc tbl k =
  match Hashtbl.find_opt tbl k with 
    | Some v -> v
    | None -> 
      let v = Hashtbl.length tbl in
      Hashtbl.add tbl k v;
      v
