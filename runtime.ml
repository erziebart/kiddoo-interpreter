open Datatypes

(* definitions for operators *)
let lib_add = arithmetic ~opv:typ_add
let lib_sub = arithmetic ~opv:typ_sub
let rec lib_neg = function
  | Value(v),u -> Value(typ_neg v), u
  | Tuple(l),u -> Tuple(List.map lib_neg l), u 
let lib_mult = arithmetic ~opv:typ_mult
let lib_div = fun (t1,u1) (t2,u2) ->
  if equal dat_true t2 then t1, u1 || u2 else 
  arithmetic ~opv:typ_div ~opu:(fun v1 v2 -> typ_equal zero v2) (t1,u1) (t2,u2)
let lib_idiv = arithmetic ~opv:typ_idiv ~opu:(fun v1 v2 -> typ_equal zero v2)
let lib_mod = arithmetic ~opv:typ_mod ~opu:(fun v1 v2 -> typ_equal zero v2) 
let lib_exp = 
  let iopu = fun i1 i2 -> false
  and fopu = fun f1 f2 -> (f1<0. && fst(modf f2)<>0.) || (f1=0. && f2=0.) in 
  arithmetic ~opv:typ_exp ~opu:(binop_on_typ ~iop:iopu ~fop:fopu)

let lib_equal = fun (t1,u1) (t2,u2) -> obj_of_bool (equal t1 t2), u1 || u2 
let lib_neq = fun (t1,u1) (t2,u2) -> obj_of_bool (not_equal t1 t2), u1 || u2 
let lib_less = fun (t1,u1) (t2,u2) -> obj_of_bool (compare t1 t2 < 0.), u1 || u2
let lib_leq = fun (t1,u1) (t2,u2) -> obj_of_bool (compare t1 t2 <= 0.), u1 || u2
let lib_greater = fun (t1,u1) (t2,u2) -> obj_of_bool (compare t1 t2 > 0.), u1 || u2
let lib_geq = fun (t1,u1) (t2,u2) -> obj_of_bool (compare t1 t2 >= 0.), u1 || u2

let lib_and = fun (t1,u1) (t2,u2) -> obj_of_bool (not_equal dat_false t1 && not_equal dat_false t2), u1 || u2
let lib_or = fun (t1,u1) (t2,u2) -> obj_of_bool (not_equal dat_false t1 || not_equal dat_false t2), u1 || u2
let lib_not = fun (t,u) -> obj_of_bool (equal dat_false t), u


(* evaluates calls to runtime library functions *)
let lib_eval name args fargs = 
	let check_args n =  
	  if List.length args = n 
	  then Array.init n (fun i -> List.nth args i)
	  else raise( Failure("wrong number of arguments for " ^ name))
	in
	let standard ~func arr = 
	  let op (t,u) = match t with
	  	| Value(v) -> Value(func (float_of_typ v)), u
	  	| Tuple(l) -> raise( Failure("wrong type of argument for " ^ name))
	  in unop_on_set ~op:op arr.(0)
	in
	match name with
	| "floor" ->
	    let arr = check_args 1 in
	    standard ~func:(fun f -> I(truncate(floor f))) arr
	| "ceil" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> I(truncate(ceil f))) arr
	| "exp" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(exp f)) arr
	| "loge" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(log f)) arr
	| "sin" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(sin f)) arr
	| "cos" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(cos f)) arr
	| "tan" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(tan f)) arr
	| "asin" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(asin f)) arr
	| "acos" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(acos f)) arr
	| "atan" -> 
	    let arr = check_args 1 in
	    standard ~func:(fun f -> F(atan f)) arr
	| "isDef" -> 
	    unop_on_set ~op:(fun (_,u) -> obj_of_bool (not u), false) (set_of_list args)

	| "print" -> (
	    match args with
	      | [] -> print_newline (); Obj(dat_false, false)
	      | _ -> print_endline (string_of_set (set_of_list args)); Obj(dat_false, false) )
	| "scan" -> 
	    ignore(check_args 0);
	    Obj(Value(F(read_float ())), false)

	| _ -> raise( Failure(name ^ ": definition not found"))