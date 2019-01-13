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

(* evaluates a call tree closure *)
let rec translate depth fconsts consts data =
  (* evaluates an expression to a value *)
  let rec eval consts fconsts calls = function
    | FloatLit(l) -> Value(F(l)), false

    | IntLit(i) -> Value(I(i)), false
  
    | Binop(e1, op, e2) -> (
        let (t1, u1) = eval consts fconsts calls e1 in 
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
              lib_or (t1,u1) (t2,u2)) )

    | Unop(uop, e) -> (
        let unop = match uop with
          | Neg -> lib_neg
          | Not -> lib_not
        in unop (eval consts fconsts calls e) )

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

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
                  then add_arg outer (List.hd params) (obj_of_list args)
                  else try List.fold_left2 add_arg outer params args with 
                    | Invalid_argument(s) -> raise(Failure("wrong number of arguments"))
                and flocals = try List.fold_left2 add_arg fouter fparams fargs with
                  | Invalid_argument(s) -> raise(Failure("wrong number of function arguments"))
                in
                let locals = List.fold_left (translate (depth+1) flocals) locals fdata.fconsts in
                eval locals flocals fdata.fcalls fdata.e
              in
              make_call values fvalues ) )

    | Tuple(exprs) -> (
        if List.length exprs = 1 then eval consts fconsts calls (List.hd exprs) else
        let ls = List.map (eval consts fconsts calls) exprs in
        obj_of_list ls )
  in

  (* translate body *)
  let consts = List.fold_left (translate (depth+1) fconsts) consts data.consts in
  let results = List.map (eval consts fconsts data.calls) data.exprs in
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