(* PRIMITIVE TYPES *)
type typ = 
  | I of int
  | F of float

let zero = I(0)

(* conversions *)
let float_of_typ = function
  | I(i) -> float i
  | F(f) -> f

let string_of_typ = function
  | I(i) -> string_of_int i
  | F(f) -> string_of_float f

(* general form for opertors *)
let binop_on_typ ~iop ~fop t1 t2 = match t1,t2 with
  | I(i1), I(i2) -> iop i1 i2
  | I(i1), F(f2) -> fop (float i1) f2
  | F(f1), I(i2) -> fop f1 (float i2)
  | F(f1), F(f2) -> fop f1 f2

let mixed_binop_on_typ ~iop ~fop t1 t2 = 
  binop_on_typ 
  ~iop:(fun i1 i2 -> I(iop i1 i2))
  ~fop:(fun f1 f2 -> F(fop f1 f2))
  t1 t2

let float_binop_on_typ ~fop t1 t2 = F(fop (float_of_typ t1) (float_of_typ t2))

let int_binop_on_typ ~iop ~fop t1 t2 = 
  binop_on_typ 
  ~iop:(fun i1 i2 -> I(iop i1 i2))
  ~fop:(fun f1 f2 -> I(fop f1 f2))
  t1 t2

let unop_on_typ ~iop ~fop = function
  | I(i) -> I(iop i)
  | F(f) -> F(fop f)

(* operators on generic type *)
let typ_add t1 t2 = mixed_binop_on_typ ~iop:(+) ~fop:(+.) t1 t2
let typ_sub t1 t2 = mixed_binop_on_typ ~iop:(-) ~fop:(-.) t1 t2
let typ_mult t1 t2 = mixed_binop_on_typ ~iop:( * ) ~fop:( *.) t1 t2
let typ_div t1 t2 = float_binop_on_typ ~fop:(/.) t1 t2
let typ_idiv t1 t2 = int_binop_on_typ ~iop:(/) ~fop:(fun f1 f2 -> truncate ((/.) f1 f2)) t1 t2
let typ_mod t1 t2 = mixed_binop_on_typ ~iop:(mod) ~fop:(mod_float) t1 t2
let typ_comp t1 t2 = compare (float_of_typ t1) (float_of_typ t2)
let typ_equal t1 t2 = (=) (float_of_typ t1) (float_of_typ t2)
let typ_neg t = unop_on_typ ~iop:(~-) ~fop:(~-.) t
let typ_exp t1 t2 = 
  let expon i1 i2 =
    let rec g p x = function
    | 0 -> x
    | i -> g (p*p) (if i mod 2 = 1 then p*x else x) (i/2)
    in g i1 1 i2
  in
  let t2 = if typ_comp t2 zero < 0 then F(float_of_typ t2) else t2 in 
  mixed_binop_on_typ ~iop:expon ~fop:( ** ) t1 t2

(* OBJECT DATA *)
type obj = data * bool
and data = 
  | Value of typ
  | Tuple of obj list

let dat_false = Value(zero)
let dat_true = Value(I(1))

(* conversions *)
let rec string_of_obj (t,u) = if u then "undef" else match t with
  | Value(v) -> string_of_typ v
  | Tuple(ls) -> "(" ^ String.concat ", " (List.map string_of_obj ls) ^ ")"

let types = List.map (fun ((t,u):obj) -> t)
let undefs = List.map (fun ((t,u):obj) -> u)
let obj_of_bool b = if b then dat_true else dat_false

let list_of_obj o = match o with
  | Value(_),_ -> [o]
  | Tuple(ls),_ -> ls

let obj_of_list ol = match ol with
  | [obj] -> obj
  | _ -> (
      let is_undef = List.fold_left (&&) true (undefs ol) in
      Tuple(ol),is_undef)

(* operations on objects *)
let rec compare t1 t2 = 
  let diff v1 v2 = (-.) (float_of_typ v1) (float_of_typ v2) in 
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

let raise_incompatible msg l1 l2 = raise(Failure(msg ^ ": " 
  ^ string_of_int(List.length l1) ^ "!=" ^ string_of_int(List.length l2)))

let rec arithmetic ~opv ?(opu=(fun v1 v2 -> false)) (t1,u1) (t2,u2)=
  let u = u1 || u2 in match t1,t2 with
  | Value(v1), Value(v2) -> Value(opv v1 v2), u || opu v1 v2
  | Value(_), Tuple(l2) -> Tuple(List.map (fun e2 -> arithmetic ~opv ~opu (t1,u1) e2 ) l2), u
  | Tuple(l1), Value(_) -> Tuple(List.map (fun e1 -> arithmetic ~opv ~opu e1 (t2,u2)) l1), u
  | Tuple(l1), Tuple(l2) -> ( try Tuple(List.map2 (arithmetic ~opv ~opu) l1 l2 ), u with
      | Invalid_argument(_) -> raise_incompatible "incompatible tuple lengths" l1 l2 )

(* SETS *)
type set = 
  | Set of int * set list
  | Obj of obj

(* useful operations on sets *)
let rec unop_on_set ~op = function
  | Obj(o) -> Obj(op o)
  | Set(id,elts) -> Set(id, List.map (unop_on_set ~op) elts)

let rec binop_on_set ~op s1 s2 = match s1, s2 with
  | Obj(o1), Obj(o2) -> Obj(op o1 o2)
  | Obj(_), Set(id, elts) -> Set(id, List.map (fun s2 -> binop_on_set ~op s1 s2) elts)
  | Set(id, elts), Obj(_) -> Set(id, List.map (fun s1 -> binop_on_set ~op s1 s2) elts)
  | Set(id1, elts1), Set(id2, elts2) ->
      let c = id1 - id2 in 
      if c < 0 then Set(id1, List.map (fun s1 -> binop_on_set ~op s1 s2) elts1)
      else if c > 0 then Set(id2, List.map (fun s2 -> binop_on_set ~op s1 s2) elts2)
      else Set(id1, List.map2 (binop_on_set ~op) elts1 elts2)

let combine_sets s1 s2 = 
  let combine (d1,u1) (d2,u2) = let u = u1 && u2 in match d1 with
    | Tuple(l) -> Tuple((d2,u2) :: l), u 
    | Value(_) -> Tuple([(d2,u2); (d1,u1)]), u
  in
  binop_on_set ~op:combine s1 s2

let rec split_set = function
  | Obj(o) -> (match o with 
      | Value(_),_ -> [Obj(o)]
      | Tuple(l),_ -> List.map (fun d -> Obj(d)) l )
  | Set(id,elts) -> (
      let matchup l1 l2 = match l1 with
        | [] -> List.map (fun x -> [x]) l2
        | _ -> (try List.map2 (fun x y -> y :: x) l1 l2 with
            | Invalid_argument(_) -> raise_incompatible "cannot split a variable length vector" l1 l2 )
      in
      List.map (fun ls -> Set(id, List.rev ls)) (List.fold_left matchup [] (List.map split_set elts)) )

(* conversions *)
let rec string_of_set = function
  | Set(_, elts) -> "[" ^ String.concat "\n" (List.map string_of_set elts) ^ "]"
  | Obj(o) -> string_of_obj o

let set_of_list sl = List.fold_left combine_sets (List.hd sl) (List.tl sl)