open Ast
open Semant

module StringMap = Map.Make(String)

(* flag a call to the runtime library *)
exception Libcall

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

(* for testing *)
let string_of_map string_of_val map = 
  let string_of_entry k v = k ^ "->" ^ string_of_val (List.hd v) ^ " " ^ string_of_int (List.length v) in
  String.concat ", " (List.map snd (StringMap.bindings (StringMap.mapi string_of_entry map)))

let string_of_metadata (data,d) = let close = match data with
    | Fundecl(_,_,close) -> close
    | Condecl(close) -> close
  in close.name ^ ":" ^ (string_of_int d)

(* evaluates a call tree closure *)
let rec translate depth fconsts consts close =
  
  (* switches to the given scope by updating constants lists *)
  let switch_scope depth params fparams args fargs inner consts fconsts = 
    let outer = map_filter_depth depth consts 
    and fouter = map_filter_depth depth fconsts
    in
    let add_arg map id value = map_add id (value,depth+1) map in
    let wargs = try List.fold_left2 add_arg outer params args with 
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
    match name with
    | "floor" -> 
        let arr = check_args 1 in 
        floor (fst arr.(0)), snd arr.(0)          
    | "ceil" -> 
        let arr = check_args 1 in 
        ceil (fst arr.(0)), snd arr.(0)          
    | "exp" -> 
        let arr = check_args 1 in
        exp (fst arr.(0)), snd arr.(0)
    | "loge" -> 
        let arr = check_args 1 in
        log (fst arr.(0)), snd arr.(0)
    | "sin" -> 
        let arr = check_args 1 in
        sin (fst arr.(0)), snd arr.(0)
    | "cos" -> 
        let arr = check_args 1 in
        cos (fst arr.(0)), snd arr.(0)
    | "tan" -> 
        let arr = check_args 1 in
        tan (fst arr.(0)), snd arr.(0)
    | "asin" -> 
        let arr = check_args 1 in
        asin (fst arr.(0)), snd arr.(0)
    | "acos" -> 
        let arr = check_args 1 in
        acos (fst arr.(0)), snd arr.(0)
    | "atan" -> 
        let arr = check_args 1 in
        atan (fst arr.(0)), snd arr.(0)
    | "isDef" -> 
        let arr = check_args 1 in
        (if (snd arr.(0)) then 0. else 1.), false

    | "print" -> (
        match args with
            [] -> print_newline (); 0., false
          | _ -> 
              let values = List.map (fst) args in
              let undefs = List.map (snd) args in
              let outputs = List.map (string_of_float) values in
              let is_undef = List.fold_left (||) false undefs in
              print_endline ((String.concat ", " outputs) ^ ", " ^ (if is_undef then "1" else "0"));
              0., is_undef )
    | "scan" -> 
        ignore(check_args 0);
        read_float (), false

    | _ -> raise( Failure(name ^ ": definition not found"))
  in

  (* evaluates an expression to a value *)
  let rec eval consts fconsts calls = 
    let float_of_bool b = if b then 1. else 0. in
    function
      FloatLit(l) -> l, false
  
    | Binop(e1, op, e2) -> (
        let (v1, u1) = eval consts fconsts calls e1 in
        match op with
          (* short circuits *)
          | Mult -> 
              (if v1 = 0. then v1, u1 else 
              let (v2, u2) = eval consts fconsts calls e2 in
              v1 *. v2, u1 || u2 )
          | Div -> (* eval denominator first *)
              (if v1 = 0. then 0., true else
              let (v2, u2) = eval consts fconsts calls e2 in
              v2 /. v1, u1 || u2)
          | And -> 
              (if v1 = 0. then v1, u1 else
              let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Or -> 
              (if v1 <> 0. then 1., u1 else
              let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Part -> 
              (if u1 then eval consts fconsts calls e2 else v1, u1 )
          
          (* eval both sides for all cases *)
          | Add -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              v1 +. v2, u1 || u2 )
          | Sub -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              v1 -. v2, u1 || u2 )
          | Exp -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              v1 ** v2, if ((v1<0. && fst(modf v2)<>0.) || (v1=0. && v2=0.)) 
                        then true else u1 || u2 )
          | Equal -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 = v2), u1 || u2 )
          | Neq -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 <> v2), u1 || u2 )
          | Less -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 < v2), u1 || u2 )
          | Leq -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 <= v2), u1 || u2 )
          | Greater -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 > v2), u1 || u2 )
          | Geq -> 
              (let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 >= v2), u1 || u2 ) )

    | Unop(uop, e) ->
        (let (v,u) = eval consts fconsts calls e in
        match uop with
            Neg -> ~-. v, u
          | Not -> float_of_bool(v = 0.), u )

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    | Call(id,fargs,args) -> 
        (let find_func id = try StringMap.find id calls with
          | Not_found -> fst (map_find id fconsts)
        in
        let (funptr,d) = try find_func id with
          | Not_found -> raise(Failure("function " ^ id ^ " missing"))
        in
        let values = List.map (eval consts fconsts calls) args
        and fvalues = List.map 
          (fun name -> try find_func name with 
            | Not_found -> raise(Failure("function argument " ^ name ^ " missing")) 
          ) fargs
        in
        match funptr with
          | Fundecl(fparams,params,close) -> 
              let fnames = List.map (fun (s,_,_) -> s) fparams in
              (let (locals, flocals) = switch_scope d params fnames values fvalues close.consts consts fconsts in
              try (*print_endline (id ^ " -- " ^ (string_of_map string_of_metadata flocals));*) eval locals flocals close.calls close.e with
                | Libcall -> lib_eval id values fvalues )
          | _ -> raise(Failure("calling a non-function")) )
     
     | Null -> raise(Libcall)
  in

  (* translate body *)
  let (locals, flocals) = switch_scope depth [] [] [] [] close.consts consts fconsts in
  let result = eval locals flocals close.calls close.e in
  match close.name with
    | "->" -> let to_print = if snd result then "undefined" else string_of_float (fst result) in print_endline to_print; consts
    | id -> map_add id (result, depth) consts
