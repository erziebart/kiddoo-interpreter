(* language data type *)
type typ = 
  | I of int
  | F of float

type obj = data * bool
and data = 
  | Value of typ
  | Tuple of obj list

let string_of_typ = function
  | I(i) -> string_of_int i
  | F(f) -> string_of_float f

let rec string_of_obj (t,u) = if u then "undef" else match t with
  | Value(v) -> string_of_typ v
  | Tuple(ls) -> "(" ^ String.concat ", " (List.map string_of_obj ls) ^ ")"

let zero = Value(I(0))
let types = List.map (fun ((t,u):obj) -> t)
let undefs = List.map (fun ((t,u):obj) -> u)
let obj_of_bool b = if b then Value(I(1)) else zero

let binop_on_typ ~iop ~fop v1 v2 = match v1,v2 with
  | I(i1), I(i2) -> iop i1 i2
  | I(i1), F(f2) -> fop (float i1) f2
  | F(f1), I(i2) -> fop f1 (float i2)
  | F(f1), F(f2) -> fop f1 f2

let unop_on_typ ~iop ~fop = function
  | I(i) -> iop i
  | F(f) -> fop f

let rec compare t1 t2 = 
  let diff v1 v2 =
    let float = 
    function
      | I(i) -> float i
      | F(f) -> f
    in (-.) (float v1) (float v2)
  in 
  match t1,t2 with
  | Value(v1), Value(v2) -> diff v1 v2
  | Value(_), Tuple(_) -> -1.
  | Tuple(_), Value(_) -> 1.
  | Tuple(l1), Tuple(l2) -> (
      let c = Pervasives.compare (List.length l1) (List.length l2) in if c <> 0 then float c else
        let types1 = types l1 and types2 = types l2 in
        try List.find (fun c -> c <> 0.) (List.map2 compare types1 types2) with
          | Not_found -> 0. )

let rec equal t1 t2 = match t1,t2 with
  | Value(v1), Value(v2) -> v1 = v2
  | Tuple(l1), Tuple(l2) -> (try List.for_all2 equal (types l1) (types l2) with
      | Invalid_argument(_) -> false)
  | _ -> false

let rec not_equal t1 t2 = match t1,t2 with
  | Value(v1), Value(v2) -> v1 <> v2
  | Tuple(l1), Tuple(l2) -> (try List.exists2 not_equal (types l1) (types l2) with
      | Invalid_argument(_) -> true)
  | _ -> true



let raise_incompatible l1 l2 = raise(Failure("incompatible tuple lengths: " 
  ^ string_of_int(List.length l1) ^ "!=" ^ string_of_int(List.length l2)))

let rec arithmetic ~opv ?(opu=(fun v1 v2 -> false)) (t1,u1) (t2,u2)=
  let u = u1 || u2 in match t1,t2 with
  | Value(v1), Value(v2) -> Value(opv v1 v2), u || opu v1 v2
  | Value(_), Tuple(l2) -> Tuple(List.map (fun e2 -> arithmetic ~opv ~opu (t1,u1) e2 ) l2), u
  | Tuple(l1), Value(_) -> Tuple(List.map (fun e1 -> arithmetic ~opv ~opu e1 (t2,u2)) l1), u
  | Tuple(l1), Tuple(l2) -> ( try Tuple(List.map2 (arithmetic ~opv ~opu) l1 l2 ), u with
      | Invalid_argument(_) -> raise_incompatible l1 l2 )

(* let list_of_obj d = match d with
  | Value(_),_ -> [d]
  | Tuple(ls),_ -> ls *)

let obj_of_list ol = match ol with
  | [obj] -> obj
  | _ -> (
      let is_undef = List.fold_left (&&) true (undefs ol) in
      Tuple(ol),is_undef)