open Ast
open Semant
open Datatypes

module StringMap = Map.Make(String)

(* data management for value mappings *)
let map_add k v map =  
  let ls = try StringMap.find k map with
    | Not_found -> []
  in
  StringMap.add k (v :: ls) map

let map_find k map = 
  List.hd (StringMap.find k map)

let map_filter_depth depth map = 
  let rec filter ls = match ls with
    | [] -> []
    | _ -> let (_,d) = List.hd ls in if d <= depth then ls else filter (List.tl ls)
  in
  StringMap.filter (fun _ ls -> ls <> []) (StringMap.map filter map)

(* evaluates a call tree closure *)
let rec translate depth fconsts consts data =
  
  (* switches to the given scope by updating constants lists *)
  let switch_scope depth params fparams args fargs inner consts fconsts = 
    let outer = map_filter_depth depth consts 
    and fouter = map_filter_depth depth fconsts
    in
    let add_arg map id value = map_add id (value,depth+1) map in
    let wargs = if List.length params = 1 
      then add_arg outer (List.hd params) (obj_of_list args)
      else try List.fold_left2 add_arg outer params args with 
        | Invalid_argument(s) -> raise(Failure("wrong number of arguments"))
    and fwargs = try List.fold_left2 add_arg fouter fparams fargs with
      | Invalid_argument(s) -> raise(Failure("wrong number of function arguments"))
    in
    List.fold_left (translate (depth+1) fwargs) wargs inner, fwargs
  in

  (* evaluates calls to runtime library functions *)
  let lib_eval name args fargs = 
    let check_args n =  
      if List.length args = n 
      then Array.init n (fun i -> List.nth args i)
      else raise( Failure("wrong number of arguments for " ^ name))
    in
    let standard ~func arr = let (t,u) = arr.(0) in match t with
      | Value(v) -> Value(func (ensure_float v)), u
      | Tuple(l) -> raise( Failure("wrong type of argument for " ^ name))
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
        let arr = check_args 1 in
        obj_of_bool (not (snd arr.(0))), false

    | "print" -> (
        match args with
          | [] -> print_newline (); zero, false
          | _ -> print_endline (string_of_obj (obj_of_list args)); zero, false )
    | "scan" -> 
        ignore(check_args 0);
        Value(F(read_float ())), false

    | _ -> raise( Failure(name ^ ": definition not found"))
  in

  (* evaluates an expression to a value *)
  let rec eval consts fconsts calls = function
    | FloatLit(l) -> Value(F(l)), false

    | IntLit(i) -> Value(I(i)), false
  
    | Binop(e1, op, e2) -> (
        let (t1, u1) = eval consts fconsts calls e1 in 
        match op with
          (* short circuits *)
          | Part -> (if u1 then eval consts fconsts calls e2 else t1, u1 )
          | Div -> (if equal zero t1 then zero, true else 
              let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> F( (/.) (float i1) (float i2) )
              and fop = fun f1 f2 -> F( (/.) f1 f2) in
              if equal (Value(I(1))) t1 then t2, u1 || u2 else
              arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
              ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2))

          (* arithmetic *)
          | Add -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> I(i1+i2)
              and fop = fun f1 f2 -> F(f1+.f2) in
              arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2))
          | Sub -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> I(i1-i2)
              and fop = fun f1 f2 -> F(f1-.f2) in
              arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2))
          | Mult -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> I(i1*i2)
              and fop = fun f1 f2 -> F(f1*.f2) in
              arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2))
          | Idiv -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> I( i1 / i2 )
              and fop = fun f1 f2 -> I( truncate(f1 /. f2)) in
              arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
              ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2))
          | Mod -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iop = fun i1 i2 -> I( i1 mod i2 )
              and fop = fun f1 f2 -> F( mod_float f1 f2) in
              arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
              ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2))
          | Exp -> (let (t2,u2) = eval consts fconsts calls e2 in
              let iopv i1 i2 =
                let rec g p x = function
                | 0 -> x
                | i -> g (p*p) (if i mod 2 = 1 then p*x else x) (i/2)
                in
                if i2 < 0 then F((float i1) ** (float i2)) else I(g i1 1 i2)
              and fopv = fun f1 f2 -> F(f1**f2) 
              and iopu = fun i1 i2 -> false
              and fopu = fun f1 f2 -> (f1<0. && fst(modf f2)<>0.) || (f1=0. && f2=0.) in 
              arithmetic ~opv:(binop_on_typ ~iop:iopv ~fop:fopv) (t1,u1) (t2,u2)
              ~opu:(binop_on_typ ~iop:iopu ~fop:fopu) )

          (* comparison *)
          | Equal -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (equal t1 t2), u1 || u2 )
          | Neq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (not_equal t1 t2), u1 || u2 )
          | Less -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (compare t1 t2 < 0.), u1 || u2 )
          | Leq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (compare t1 t2 <= 0.), u1 || u2 )
          | Greater -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (compare t1 t2 > 0.), u1 || u2 )
          | Geq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (compare t1 t2 >= 0.), u1 || u2 )

          (* logical *)
          | And -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (not_equal zero t1 && not_equal zero t2), u1 || u2)
          | Or -> (let (t2,u2) = eval consts fconsts calls e2 in 
              obj_of_bool (not_equal zero t1 || not_equal zero t2), u1 || u2) )

    | Unop(uop, e) -> (
        let t,u = eval consts fconsts calls e in
        match uop with
          | Neg -> (
              let rec neg = function
                | Value(v),u -> Value(unop_on_typ ~iop:(fun i -> I(~-i)) ~fop:(fun f -> F(~-.f)) v), u
                | Tuple(l),u -> Tuple(List.map neg l), u
              in neg (t,u) )
          | Not -> obj_of_bool (equal zero t), u )

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    | Call(id,fargs,args) -> 
        (let find_func id = try StringMap.find id calls with
          | Not_found -> fst (map_find id fconsts)
        in
        let fdata = try find_func id with
          | Not_found -> raise(Failure("function " ^ id ^ " missing"))
        in 
        let values = List.map (eval consts fconsts calls) args
        and fvalues = List.map 
          (fun name -> try find_func name with 
            | Not_found -> raise(Failure("function argument " ^ name ^ " missing")) 
          ) fargs
        in
        let fnames = List.map (fun (s,_,_) -> s) fdata.fparams in
        let (locals, flocals) = switch_scope fdata.depth fdata.params fnames values fvalues fdata.fconsts consts fconsts in
        match fdata.e with
          | Tuple([]) -> lib_eval id values fvalues
          | _ -> eval locals flocals fdata.fcalls fdata.e )

    | Tuple(exprs) -> (
        if List.length exprs = 1 then eval consts fconsts calls (List.hd exprs) else
        let ls = List.map (eval consts fconsts calls) exprs in
        obj_of_list ls )
  in

  (* translate body *)
  let (locals, flocals) = switch_scope depth [] [] [] [] data.consts consts fconsts in
  let results = List.map (eval locals flocals data.calls) data.exprs in
  match data.names with
    | [id] -> (
        let result = obj_of_list results in
        match id with
          | "->" -> let to_print = string_of_obj result in print_endline to_print; consts
          | _ -> map_add id (result, depth) consts )
    | _ -> (
        let results = match results with
          | [dat] -> (match dat with
             | Tuple(l),_ -> l
             | Value(_),_ -> raise(Failure("assigning single value in multiple assignment")) )
          | _ -> results
        in
        try List.fold_left2 (fun map id t -> map_add id (t, depth) map) consts data.names results with
          | Invalid_argument(_) -> raise(Failure("incompatible tuple assignment: " 
              ^ string_of_int(List.length data.names) ^ "!=" ^ string_of_int(List.length results))) )