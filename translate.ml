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
            binop_on_set ~op:lib_div s2 s1 )

        (* no short circuit *)
        | _,_ -> (
            let s2 = eval consts fconsts calls e2 in
            let op (t1,u1) (t2,u2) = match op with
              | Part -> (if u1 then t2,u2 else t1,u1 )

              (* arithmetic *)
              | Add -> lib_add (t1,u1) (t2,u2)
              | Sub -> lib_sub (t1,u1) (t2,u2)
              | Mult -> lib_mult (t1,u1) (t2,u2)
              | Div -> lib_div (t2,u2) (t1,u1)
              | Idiv -> lib_idiv (t2,u2) (t1,u1)
              | Mod -> lib_mod (t2,u2) (t1,u1)
              | Exp -> lib_exp (t1,u1) (t2,u2)

              (* comparison *)
              | Equal -> lib_equal (t1,u1) (t2,u2)
              | Neq -> lib_neq (t1,u1) (t2,u2)
              | Less -> lib_less (t1,u1) (t2,u2)
              | Leq -> lib_leq (t1,u1) (t2,u2)
              | Greater -> lib_greater (t1,u1) (t2,u2)
              | Geq -> lib_geq (t1,u1) (t2,u2)

              (* logical *)
              | And -> lib_and (t1,u1) (t2,u2)
              | Or -> lib_or (t1,u1) (t2,u2)
            in
            binop_on_set ~op:op s1 s2 ) )

    | Unop(uop, e) -> (
        let unop = match uop with
          | Neg -> lib_neg
          | Not -> lib_not
        in unop_on_set ~op:unop (eval consts fconsts calls e))

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    | Access(e,exprs) -> (
        let set = eval consts fconsts calls e in
        let indexes = List.map (eval consts fconsts calls) exprs in

        let rec access_member s idxs = 
          let assert_int = 
          function
            | Value(I(idx)),u -> idx,u
            | _ -> raise(Failure("set index must be an integer"))
          in
          let get_nth ls idx = 
            let len = List.length ls in
            if len > 0 then
              let i = idx mod len in
              let i = if i < 0 then len + i else i in
              List.nth ls i
            else
              raise(Failure("cannot index an empty set"))
          in
          match s,idxs with
          | Set(_,elts), hd :: tl -> (let idx,u = assert_int hd in 
              if u then Obj(dat_false, true) else access_member (get_nth elts idx) tl)
          | Set(_,_), [] -> s
          | Obj(_,_), _ -> s
        in
        
        let rec map_access = function
          | Obj(t,u) -> access_member set (list_of_obj (t,u))
          | Set(id,elts) -> Set(id, List.map map_access elts)
        in 
        map_access (set_of_list indexes)
        )

    | Call(id,fargs,args) -> (
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
                  then add_arg outer (List.hd params) (Obj(obj_of_list args))
                  else try List.fold_left2 add_arg outer params (List.map (fun e -> Obj(e)) args) with 
                    | Invalid_argument(s) -> raise(Failure("wrong number of arguments for " ^ id))
                and flocals = try List.fold_left2 add_arg fouter fparams fargs with
                  | Invalid_argument(s) -> raise(Failure("wrong number of function arguments for " ^ id))
                in
                let locals = List.fold_left (translate (depth+1) flocals) locals fdata.fconsts in
                eval locals flocals fdata.fcalls fdata.e
              in

              (* calls the function for all arguments in the set *)
              let rec map_call = function
                | Obj(t,u) -> make_call (list_of_obj (t,u)) fvalues
                | Set(id,elts) -> Set(id, List.map map_call elts)
              in
              map_call (set_of_list values) ) )

    | Tuple(exprs) -> (set_of_list (List.map (eval consts fconsts calls) exprs) )

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
        Set(get_uuid (), List.rev (List.fold_left parse_item [] items)) )
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