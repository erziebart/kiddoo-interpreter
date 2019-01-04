(* language data type *)
type data = typ * bool
and typ = 
  | Value of float
  | Tuple of data list

let rec string_of_data (v,u) = if u then "undef" else match v with
  | Value(v) -> string_of_float v
  | Tuple(ls) -> "(" ^ String.concat ", " (List.map string_of_data ls) ^ ")"

let zero = Value(0.)
let types = List.map (fun ((t,u):data) -> t)
let undefs = List.map (fun ((t,u):data) -> u)

let data_of_bool b = if b then Value(1.) else zero 

let rec compare t1 t2 = match t1,t2 with
  | Value(v1), Value(v2) -> v1 -. v2
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

(* let list_of_data d = match d with
  | Value(_),_ -> [d]
  | Tuple(ls),_ -> ls *)

let data_of_list dl = match dl with
  | [data] -> data
  | _ -> (
      let is_undef = List.fold_left (&&) true (undefs dl) in
      Tuple(dl),is_undef)