open Ast
open Semant
open Datatypes
open Runtime

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

(* unique set ids *)
let set_uuid = ref 0
let get_uuid () = let res = !set_uuid in incr set_uuid; res

(* evaluates a call tree closure *)
let rec translate depth fconsts consts data =
  (* evaluates an expression to a value *)
  let rec eval consts fconsts calls = function
    | FloatLit(l) -> Obj(Value(F(l)), false)

    | IntLit(i) -> Obj(Value(I(i)), false)
  
    | Binop(e1, op, e2) -> (
        let s1 = eval consts fconsts calls e1 in 
        match s1, op with
        (* short circuits *)
        | Obj(t1,u1), Part -> (if u1 then eval consts fconsts calls e2 else s1 )
        | Obj(t1,u1), Div -> (
            if equal dat_false t1 then Obj(dat_false, true) else 
            let s2 = eval consts fconsts calls e2 in
            binop_on_set ~op:lib_div s1 s2 )
            (* if equal zero t1 then Obj(zero, true) else 
            let s2 = eval consts fconsts calls e2 in
            let div (t1,u1) (t2,u2) = 
              let iop = fun i1 i2 -> F( (/.) (float i1) (float i2) )
              and fop = fun f1 f2 -> F( (/.) f1 f2) in
              if equal (Value(I(1))) t1 then t2, u1 || u2 else
              arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
              ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2)
            in 
            binop_on_set ~op:div s1 s2 ) *)

        (* no short circuit *)
        | _,_ -> (
            let s2 = eval consts fconsts calls e2 in
            let op (t1,u1) (t2,u2) = match op with
              | Part -> (if u1 then t2,u2 else t1,u1 )

              (* arithmetic *)
              | Add -> lib_add (t1,u1) (t2,u2)
                  (* let iop = fun i1 i2 -> I(i1+i2)
                  and fop = fun f1 f2 -> F(f1+.f2) in
                  arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2)) *)
            | Sub -> lib_sub (t1,u1) (t2,u2)
                (* let iop = fun i1 i2 -> I(i1-i2)
                and fop = fun f1 f2 -> F(f1-.f2) in
                arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2)) *)
            | Mult -> lib_mult (t1,u1) (t2,u2)
                (* let iop = fun i1 i2 -> I(i1*i2)
                and fop = fun f1 f2 -> F(f1*.f2) in
                arithmetic ~opv:(binop_on_typ ~iop:iop ~fop:fop) (t1,u1) (t2,u2)) *)
            | Div -> lib_div (t1,u1) (t2,u2)
                (* let iop = fun i1 i2 -> F( (/.) (float i1) (float i2) )
                and fop = fun f1 f2 -> F( (/.) f1 f2) in
                if equal (Value(I(1))) t1 then t2, u1 || u2 else
                arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
                ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2)) *)
            | Idiv -> lib_idiv (t1,u1) (t2,u2)
                (* let iop = fun i1 i2 -> I( i1 / i2 )
                and fop = fun f1 f2 -> I( truncate(f1 /. f2)) in
                arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
                ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2)) *)
            | Mod -> lib_mod (t1,u1) (t2,u2)
                (* let iop = fun i1 i2 -> I( i1 mod i2 )
                and fop = fun f1 f2 -> F( mod_float f1 f2) in
                arithmetic ~opv:(fun v1 v2 -> binop_on_typ ~iop:iop ~fop:fop v2 v1) 
                ~opu:(fun v1 v2 -> unop_on_typ ~iop:((=) 0) ~fop:((=) 0.) v1) (t1,u1) (t2,u2)) *)
            | Exp -> lib_exp (t1,u1) (t2,u2)
                (* let iopv i1 i2 =
                  let rec g p x = function
                  | 0 -> x
                  | i -> g (p*p) (if i mod 2 = 1 then p*x else x) (i/2)
                  in
                  if i2 < 0 then F((float i1) ** (float i2)) else I(g i1 1 i2)
                and fopv = fun f1 f2 -> F(f1**f2) 
                and iopu = fun i1 i2 -> false
                and fopu = fun f1 f2 -> (f1<0. && fst(modf f2)<>0.) || (f1=0. && f2=0.) in 
                arithmetic ~opv:(binop_on_typ ~iop:iopv ~fop:fopv) (t1,u1) (t2,u2)
                ~opu:(binop_on_typ ~iop:iopu ~fop:fopu) ) *)

            (* comparison *)
            | Equal -> (* (obj_of_bool (equal t1 t2), u1 || u2 ) *) lib_equal (t1,u1) (t2,u2)
            | Neq -> (* (obj_of_bool (not_equal t1 t2), u1 || u2 ) *) lib_neq (t1,u1) (t2,u2)
            | Less -> (* (obj_of_bool (compare t1 t2 < 0.), u1 || u2 ) *) lib_less (t1,u1) (t2,u2)
            | Leq -> (* (obj_of_bool (compare t1 t2 <= 0.), u1 || u2 ) *) lib_leq (t1,u1) (t2,u2)
            | Greater -> (* (obj_of_bool (compare t1 t2 > 0.), u1 || u2 ) *) lib_greater (t1,u1) (t2,u2)
            | Geq -> (* (obj_of_bool (compare t1 t2 >= 0.), u1 || u2 ) *) lib_geq (t1,u1) (t2,u2)

            (* logical *)
            | And -> (* (obj_of_bool (not_equal zero t1 && not_equal zero t2), u1 || u2) *) lib_and (t1,u1) (t2,u2)
            | Or -> (* (obj_of_bool (not_equal zero t1 || not_equal zero t2), u1 || u2) *) lib_or (t1,u1) (t2,u2)
            in
            binop_on_set ~op:op s1 s2 ) )

        (* let (t1, u1) = eval consts fconsts calls e1 in 
        match op with
          (* short circuits *)
          | Part -> (if u1 then eval consts fconsts calls e2 else t1, u1 )
          | Div -> (if equal dat_false t1 then dat_false, true else 
              let (t2,u2) = eval consts fconsts calls e2 in
              if equal dat_true t1 then t2, u1 || u2 else
              lib_div (t2,u2) (t1,u1))

          (* arithmetic *)
          | Add -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_add (t1,u1) (t2,u2))
          | Sub -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_sub (t1,u1) (t2,u2))
          | Mult -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_mult (t1,u1) (t2,u2))
          | Idiv -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_idiv (t1,u1) (t2,u2))
          | Mod -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_mod (t1,u1) (t2,u2))
          | Exp -> (let (t2,u2) = eval consts fconsts calls e2 in
              lib_exp (t1,u1) (t2,u2) )

          (* comparison *)
          | Equal -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_equal (t1,u1) (t2,u2) )
          | Neq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_neq (t1,u1) (t2,u2) )
          | Less -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_less (t1,u1) (t2,u2) )
          | Leq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_leq (t1,u1) (t2,u2) )
          | Greater -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_greater (t1,u1) (t2,u2) )
          | Geq -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_geq (t1,u1) (t2,u2) )

          (* logical *)
          | And -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_and (t1,u1) (t2,u2))
          | Or -> (let (t2,u2) = eval consts fconsts calls e2 in 
              lib_or (t1,u1) (t2,u2)) ) *)

    | Unop(uop, e) -> (
        let unop = match uop with
          | Neg -> lib_neg
          | Not -> lib_not
        in unop_on_set ~op:unop (eval consts fconsts calls e))

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    (*| Call(id,fargs,args) -> (
        (* locate the function data *)
        let find_func id = try StringMap.find id calls with
          | Not_found -> fst (map_find id fconsts)
        in
        let fdata = try find_func id with
          | Not_found -> raise(Failure("function " ^ id ^ " missing"))
        in 

        (* compute the arguments *)        
        let values = List.map (eval consts fconsts calls) args
        and fvalues = List.map 
          (fun name -> try find_func name with 
            | Not_found -> raise(Failure("function argument " ^ name ^ " missing")) 
          ) fargs
        in

        (* match with program or runtime library function *)
        match fdata.e with
          | Tuple([]) -> lib_eval id values fvalues
          | _ -> (
              (* function paramters *)
              let params = fdata.params
              and fparams = List.map (fun (s,_,_) -> s) fdata.fparams in

              (* filter away variables that are no longer visible *)
              let depth = fdata.depth in
              let outer = map_filter_depth depth consts 
              and fouter = map_filter_depth depth fconsts
              in

              (* produces the result of calling the function with given arguments *)
              let make_call args fargs = 
                let add_arg map id value = map_add id (value,depth+1) map in
                let locals = if List.length params = 1 
                  then add_arg outer (List.hd params) (obj_of_list args)
                  else try List.fold_left2 add_arg outer params args with 
                    | Invalid_argument(s) -> raise(Failure("wrong number of arguments"))
                and flocals = try List.fold_left2 add_arg fouter fparams fargs with
                  | Invalid_argument(s) -> raise(Failure("wrong number of function arguments"))
                in
                let locals = List.fold_left (translate (depth+1) flocals) locals fdata.fconsts in
                eval locals flocals fdata.fcalls fdata.e
              in
              make_call values fvalues ) )*)

    | Tuple(exprs) -> (
        let elements = List.map (eval consts fconsts calls) exprs in
        List.fold_left combine_sets (List.hd elements) (List.tl elements) )      
        (* if List.length exprs = 1 then eval consts fconsts calls (List.hd exprs) else
        let ls = List.map (eval consts fconsts calls) exprs in
        obj_of_list ls ) *)

    | Set(items) -> ( 
        let parse_item ls = function
          | Element(expr) -> eval consts fconsts calls expr :: ls
          | Range(range) -> (
              let eval_opt default = function
                | Expr(e) -> (
                    let result = eval consts fconsts calls e in
                    match result with
                    | Obj(Value(t),u) -> if u then raise(Failure("range must be defined")) else t
                    | Obj(Tuple(_),_) -> raise(Failure("cannot define range using a vector"))
                    | Set(_) -> raise(Failure("cannot define range using a set")) )
                | None -> default
              in 
              let start = eval_opt (I(0)) range.start
              and stop = eval_opt (I(0)) range.stop
              and step = eval_opt (I(1)) range.step
              in match start,stop,step with
                | I(start), I(stop), I(step) -> (
                    let rec make_range cur = if cur < stop then (Obj(Value(I(cur)),false)) :: make_range (cur + step) else [] in
                    List.rev_append (make_range start) ls )
                | _ -> (
                    let start,stop,step = float_of_typ start, float_of_typ stop, float_of_typ step in
                    let rec make_range cur = if cur < stop then (Obj(Value(F(cur)),false)) :: make_range (cur +. step) else [] in
                    List.rev_append (make_range start) ls ) )
        in
        Set(get_uuid (), List.fold_left parse_item [] items) )
  in

  (* translate body *)
  let consts = List.fold_left (translate (depth+1) fconsts) consts data.consts in
  let results = List.map (eval consts fconsts data.calls) data.exprs in
  match data.names with
    | [id] -> (
        let result = set_of_list results in
        match id with
          | "->" -> let to_print = string_of_set result in print_endline to_print; consts
          | _ -> map_add id (result, depth) consts )
    | _ -> (
        let results = match results with
          | [dat] -> split_set dat
          | _ -> results
        in
        try List.fold_left2 (fun map id t -> map_add id (t, depth) map) consts data.names results with
          | Invalid_argument(_) -> raise_incompatible "incompatible tuple assignment" data.names results )