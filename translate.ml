open Ast
open Semant

module StringMap = Map.Make(String)

(* flag a call to the runtime library *)
exception NullExpr

(* language data type *)
type data = typ * bool
and typ = 
  | Value of float
  | Tuple of data list

let rec string_of_data (v,u) = if u then "undef" else match v with
  | Value(v) -> string_of_float v
  | Tuple(ls) -> "(" ^ String.concat ", " (List.map string_of_data ls) ^ ")"

let equals v1 = function
  | Value(v2) -> v1 = v2
  | Tuple(_) -> false

let not_equals v1 = function
  | Value(v2) -> v1 <> v2
  | Tuple(_) -> false

let raise_incompatible l1 l2 = raise(Failure("incompatible tuple lengths: " 
  ^ string_of_int(List.length l1) ^ "!=" ^ string_of_int(List.length l2)))

let to_list d = match d with
  | Value(_),_ -> [d]
  | Tuple(ls),_ -> ls

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
(*
let string_of_map string_of_val map = 
  let string_of_entry k v = k ^ "->" ^ string_of_val (List.hd v) ^ " " ^ string_of_int (List.length v) in
  String.concat ", " (List.map snd (StringMap.bindings (StringMap.mapi string_of_entry map)))

let string_of_metadata (data,d) = let close = match data with
    | Fundecl(_,_,close) -> close
    | Condecl(close) -> close
  in close.name ^ ":" ^ (string_of_int d)
*)

(* evaluates a call tree closure *)
let rec translate depth fconsts consts (names,close) =
  
  (* switches to the given scope by updating constants lists *)
  let switch_scope depth params fparams args fargs inner consts fconsts = 
    let outer = map_filter_depth depth consts 
    and fouter = map_filter_depth depth fconsts
    in
    let add_arg map id value = map_add id (value,depth+1) map in
    let wargs = try List.fold_left2 add_arg outer params [args] with 
      | Invalid_argument(s) -> try List.fold_left2 add_arg outer params (to_list args) with 
      | Invalid_argument(s) -> raise(Failure("wrong number of arguments"))
    and fwargs = try List.fold_left2 add_arg fouter fparams fargs with
      | Invalid_argument(s) -> raise(Failure("wrong number of function arguments"))
    in
    List.fold_left (translate (depth+1) fwargs) wargs inner, fwargs
  in

  (* evaluates calls to runtime library functions *)
  let lib_eval name args fargs = 
    let check_args n =  
      let args = to_list args in
      if List.length args = n 
      then Array.init n (fun i -> List.nth args i)
      else raise( Failure("wrong number of arguments for " ^ name))
    in
    let standard func arr = let (t,u) = arr.(0) in match t with
      | Value(v) -> Value(func v), u
      | Tuple(l) -> raise( Failure("wrong type of argument for " ^ name))
    in
    match name with
    | "floor" -> 
        let arr = check_args 1 in standard floor arr       
    | "ceil" -> 
        let arr = check_args 1 in standard ceil arr        
    | "exp" -> 
        let arr = check_args 1 in standard exp arr
    | "loge" -> 
        let arr = check_args 1 in standard log arr
    | "sin" -> 
        let arr = check_args 1 in standard sin arr
    | "cos" -> 
        let arr = check_args 1 in standard cos arr
    | "tan" -> 
        let arr = check_args 1 in standard tan arr
    | "asin" -> 
        let arr = check_args 1 in standard asin arr
    | "acos" -> 
        let arr = check_args 1 in standard acos arr
    | "atan" -> 
        let arr = check_args 1 in standard atan arr
    | "isDef" -> 
        let arr = check_args 1 in
        (if (snd arr.(0)) then Value(0.) else Value(1.)), false

    | "print" -> (
        match args with
          | Tuple([]),_ -> print_newline (); Value(0.), false
          | _,_ -> print_endline (string_of_data args); Value(0.), false )
              (* (* let values = List.map (fst) args in *)
              let undefs = List.map (snd) args in
              let outputs = List.map (string_of_data) args in
              let is_undef = List.fold_left (||) false undefs in
              print_endline (String.concat ", " outputs) (* ^ ", " ^ (if is_undef then "1" else "0")) *);
              Value(0.), is_undef ) *)
    | "scan" -> 
        ignore(check_args 0);
        Value(read_float ()), false

    | _ -> raise( Failure(name ^ ": definition not found"))
  in

  (* evaluates an expression to a value *)
  let rec eval consts fconsts calls = 
    let float_of_bool b = if b then 1. else 0. in  
    function
      FloatLit(l) -> Value(l), false
  
    | Binop(e1, op, e2) -> (
        let rec binop op (t1,u1) (t2,u2) = (match (t1, t2) with
          | Value(v1), Value(v2) -> Value(op v1 v2)
          | Value(_), Tuple(l2) -> Tuple(List.map (binop op (t1,u1)) l2)
          | Tuple(l1), Value(_) -> Tuple(List.map (fun v -> binop op v (t2,u2)) l1)
          | Tuple(l1), Tuple(l2) -> ( try Tuple(List.map2 (binop op) l1 l2 ) with
              | Invalid_argument(s) -> raise_incompatible l1 l2 ) ), u1 || u2
        in

        let (t1, u1) = eval consts fconsts calls e1 in
        match op with
          (* short circuits *)
          | Mult -> 
              (if equals 0. t1 then t1, u1 else 
              let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> v1 *. v2) (t1,u1) (t2,u2) )
          | Div -> (* eval denominator first *)
              (let rec div (t1,u1) (t2,u2) = match (t1,t2) with
                | Value(v1), Value(v2) -> (Value(v2 /. v1), 
                    v1 = 0. || u1 || u2 )
                | Value(_), Tuple(l2) -> Tuple(List.map (div (t1,u1)) l2), u1 || u2
                | Tuple(l1), Value(_) -> Tuple(List.map (fun v -> div v (t2,u2)) l1), u1 || u2
                | Tuple(l1), Tuple(l2) -> ( try Tuple(List.map2 div l1 l2), u1 || u2 with
                    | Invalid_argument(s) -> raise_incompatible l1 l2 )
              in
              if equals 0. t1 then Value(0.), true else
              let (t2, u2) = eval consts fconsts calls e2 in
              div (t1,u1) (t2,u2) )
          | And -> 
              (if equals 0. t1 then t1, u1 else
              let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1<>0. && v2<>0.)) (t1,u1) (t2,u2) )
          | Or -> 
              (if not_equals 0. t1 then Value(1.), u1 else
              let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1<>0. || v2<>0.)) (t1,u1) (t2,u2) )
          | Part -> 
              (if u1 then eval consts fconsts calls e2 else t1, u1 )
          
          (* eval both sides for all cases *)
          | Add -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> v1 +. v2) (t1,u1) (t2,u2) )
          | Sub -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> v1 -. v2) (t1,u1) (t2,u2) )
          | Exp -> (
              let rec exp (t1,u1) (t2,u2) = match (t1, t2) with
                | Value(v1), Value(v2) -> (Value(v1 ** v2), 
                    (v1<0. && fst(modf v2)<>0.) || (v1=0. && v2=0.) || u1 || u2 )
                | Value(_), Tuple(l2) -> Tuple(List.map (exp (t1,u1)) l2), u1 || u2
                | Tuple(l1), Value(_) -> Tuple(List.map (fun v -> exp v (t2,u2)) l1), u1 || u2
                | Tuple(l1), Tuple(l2) -> ( try Tuple(List.map2 exp l1 l2), u1 || u2 with
                    | Invalid_argument(s) -> raise_incompatible l1 l2 )
              in
              let (t2, u2) = eval consts fconsts calls e2 in exp (t1,u1) (t2,u2) )
          | Equal -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 = v2)) (t1,u1) (t2,u2) )
          | Neq -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 <> v2)) (t1,u1) (t2,u2) )
          | Less -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 < v2)) (t1,u1) (t2,u2) )
          | Leq -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 <= v2)) (t1,u1) (t2,u2) )
          | Greater -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 > v2)) (t1,u1) (t2,u2) )
          | Geq -> 
              (let (t2, u2) = eval consts fconsts calls e2 in
              binop (fun v1 v2 -> float_of_bool(v1 >= v2)) (t1,u1) (t2,u2) ) )

(*     | Part(e1, e2) -> (
        let (t1, u1) = eval consts fconsts calls e1 in
        if u1 then eval consts fconsts calls e2 else t1, u1 ) *)

    | Unop(uop, e) ->
        (let rec unop uop (t,u) = (match t with
          | Value(v) -> Value(uop v)
          | Tuple(l) -> Tuple(List.map (unop uop) l) ), u
        in
        let (t,u) = eval consts fconsts calls e in
        match uop with
            Neg -> unop (fun v -> ~-. v) (t,u)
          | Not -> unop (fun v -> float_of_bool(v = 0.)) (t,u) )

    | Var(id) -> 
        (try fst (map_find id consts) with
          | Not_found -> raise(Failure("variable " ^ id ^ " missing")) )

    | Call(id,fargs,args) -> 
        (let find_func id = try StringMap.find id calls with
          | Not_found -> fst (map_find id fconsts)
        in
        let ((fparams,params,close),d) = try find_func id with
          | Not_found -> raise(Failure("function " ^ id ^ " missing"))
        in 
        let values = try eval consts fconsts calls args with
          | NullExpr -> Tuple([]), false
        and fvalues = List.map 
          (fun name -> try find_func name with 
            | Not_found -> raise(Failure("function argument " ^ name ^ " missing")) 
          ) fargs
        in
        let fnames = List.map (fun (s,_,_) -> s) fparams in
        let (locals, flocals) = switch_scope d params fnames values fvalues close.consts consts fconsts in
        match close.e with
          | [] -> lib_eval id values fvalues
          | exprs -> let e = Ast.Tuple(exprs) in eval locals flocals close.calls e )
        (* try eval locals flocals close.calls close.e with
          | NullExpr -> lib_eval id values fvalues ) *)

    | Tuple(exprs) -> (
        let ls = List.map (eval consts fconsts calls) exprs in
        let undefs = List.map (snd) ls in
        Tuple(ls), List.fold_left (&&) true undefs )
     
    | Null -> raise(NullExpr)
  in

  (* translate body *)
  let (locals, flocals) = switch_scope depth [] [] (Tuple([]),false) [] close.consts consts fconsts in
  match names with
    | [id] -> (let result = eval locals flocals close.calls (Tuple(close.e)) in match id with
        | "->" -> let to_print = string_of_data result in print_endline to_print; consts
        | n -> map_add id (result, depth) consts )
    | ids -> (
        let results = List.map (eval locals flocals close.calls) close.e in
        try List.fold_left2 (fun map id t -> map_add id (t, depth) map) consts ids results with
          | Invalid_argument(_) -> raise(Failure("incompatible tuple assignment: " 
              ^ string_of_int(List.length ids) ^ "!=" ^ string_of_int(List.length results))) )

 (*  let result = List.map (eval locals flocals close.calls) close.e in
  match names with
    | ["->"] -> let to_print = String.concat ", " (List.map string_of_data result) in print_endline to_print; consts
    | [id] -> map_add id ((Tuple(result),false), depth) consts
    | ids -> match result with
        | Tuple(l),_ -> (try List.fold_left2 (fun map id t -> map_add id (t, depth) map) consts ids l with
           | Invalid_argument(_) -> raise(Failure("incompatible tuple assignments: " 
              ^ string_of_int(List.length ids) ^ "!=" ^ string_of_int(List.length l))) )
        | Value(_),_ -> raise(Failure("incompatible tuple assignment: "
            ^ string_of_int(List.length ids) ^ "!=1")) *)
