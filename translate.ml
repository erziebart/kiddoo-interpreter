open Ast
open Semant

module StringMap = Map.Make(String)

(* flag a call to the runtime library *)
exception Libcall

(* evaluates a call tree closure *)
let rec translate depth fconsts consts close =
  
  (* switches to the given scope by updating constants lists *)
  let switch_scope depth params fparams args fargs inner consts fconsts = 
    let depth_filter _ (_,d) = d <= depth in
    let outer = StringMap.filter depth_filter consts 
    and fouter = StringMap.filter depth_filter fconsts
    in
    let add_arg map id value = StringMap.add id (value,depth+1) map in
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
        match op with
          | Div -> (* eval denominator first *)
              (let (v2, u2) = eval consts fconsts calls e2 in
              if v2 = 0. then 0., true else
              let (v1, u1) = eval consts fconsts calls e1 in
              v1 /. v2, u1 || u2)

          (* short circuits *)
          | Mult -> 
              (let (v1, u1) = eval consts fconsts calls e1 in
              if v1 = 0. then v1, u1 else 
              let (v2, u2) = eval consts fconsts calls e2 in
              v1 *. v2, u1 || u2 )
          | And -> 
              (let (v1, u1) = eval consts fconsts calls e1 in
              if v1 = 0. then v1, u1 else
              let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Or -> 
              (let (v1, u1) = eval consts fconsts calls e1 in
              if v1 <> 0. then 1., u1 else
              let (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Part -> 
              (let (v1,u1) = eval consts fconsts calls e1 in
              if u1 then eval consts fconsts calls e2 else v1, u1 )
          
          (* eval both sides for all cases *)
          | Add -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              v1 +. v2, u1 || u2 )
          | Sub -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              v1 -. v2, u1 || u2 )
          | Exp -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              v1 ** v2, if ((v1<0. && fst(modf v2)<>0.) || (v1=0. && v2=0.)) 
                        then true else u1 || u2 )
          | Equal -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 = v2), u1 || u2 )
          | Neq -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 <> v2), u1 || u2 )
          | Less -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 < v2), u1 || u2 )
          | Leq -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 <= v2), u1 || u2 )
          | Greater -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 > v2), u1 || u2 )
          | Geq -> 
              (let (v1, u1) = eval consts fconsts calls e1 
              and (v2, u2) = eval consts fconsts calls e2 in
              float_of_bool(v1 >= v2), u1 || u2 ) )

    | Unop(uop, e) ->
        (let (v,u) = eval consts fconsts calls e in
        match uop with
            Neg -> ~-. v, u
          | Not -> float_of_bool(v = 0.), u )

    | Var(id) -> 
        (try fst (StringMap.find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    | Call(id,fargs,args) -> 
        (let find_func id = try StringMap.find id calls with
          | Not_found -> StringMap.find id fconsts
        in
        let (funptr,d) = try find_func id with
          | Not_found -> raise(Failure("function " ^ id ^ " missing"))
        in
        let values = List.map (eval consts fconsts calls) args
        and fvalues = List.map 
          (fun name -> try fst (find_func name) with 
            | Not_found -> raise(Failure("function argument " ^ name ^ " missing")) 
          ) fargs
        in
        match funptr with
          | Fundecl(fparams,params,close) -> 
              let fnames = List.map (fun (s,_,_) -> s) fparams in
              (let (locals, flocals) = switch_scope d params fnames values fvalues close.consts consts fconsts in
              try eval locals flocals close.calls close.e with
                | Libcall -> lib_eval id values fvalues )
          | _ -> raise(Failure("calling a non-function")) )
     
     | Null -> raise(Libcall)
  in

  (* translate body *)
  let (locals, flocals) = switch_scope depth [] [] [] [] close.consts consts fconsts in
  let result = eval locals flocals close.calls close.e in
  match close.name with
    | "->" -> let to_print = if snd result then "undefined" else string_of_float (fst result) in print_endline to_print; consts
    | id -> StringMap.add id (result, depth) consts
