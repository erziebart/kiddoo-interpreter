open Ast
(*open Printf*)

module StringMap = Map.Make(String)

(* Call Tree *)
type node =
    Root
  | Func of func * def * node(*parent*)
  | Fcall of (string*node)list(*fargs*) * (string*(float*bool))list(*args*) * (float*bool)StringMap.t(*consts*) * node(*parent*)

(* flag a call to the runtime library *)
exception LibCall

let rec translate globals consts ast =
  (* evaluates calls to runtime library functions *)
  let lib_eval name args = 
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

  (* create a string map of name->func_node along the given path to root for the given list of names *)
  let rec path_find path names map = 
    match path with
        Root -> map
      | Fcall(fargs,_,_,parent) -> (
          let check_list (names, nodes) (s,n) =
            if List.mem s names 
            then List.filter (fun name -> name <> s) names, (s, n) :: nodes
            else names, nodes 
          in
          let (names',nodelist) = List.fold_left check_list (names, []) fargs in
          let nmap = path_find parent names' map in
          let add_node map (s,n) = StringMap.add s n map in
          List.fold_left add_node nmap nodelist )
      | Func(func, _, parent) -> 
          let name = func.fname in
          if List.mem name names then (
            let names' = List.filter (fun s -> s <> name) names in
            let nmap = path_find parent names' map in
            StringMap.add name path nmap
          )
          else (
            path_find parent names map
          )
  in

  (* find an argument value along the path to the root *)
  let rec path_find_value path name = (
    match path with
        Root -> raise(Not_found)
      | Fcall(_,args,consts,parent) -> (
          try (StringMap.find name consts) with
          | Not_found -> try (snd (List.find (fun (s,v) -> s = name) args)) with
          | Not_found -> path_find_value parent name )
      | Func(_,_, parent) -> path_find_value parent name )
  in

  (* find a func node along the path to the root *)
  let rec path_find_func path name =
    match path with
        Root -> raise(Not_found)
      | Fcall(fargs,_,_,parent) -> (
          try (snd (List.find (fun (s,n) -> s = name) fargs)) with
            | Not_found -> path_find_func parent name )
      | Func(func, _, parent) -> 
          if (func.fname = name) then path else path_find_func parent name
  in
  
  (* make a new call tree branch with the given root *)
  let make_branch root decls =
    let make_node parent = function
        Function(func, def) -> Func(func, def, parent)
      | Constant(_,_) -> parent
      | _ -> raise(Failure("Can only nest definitions and constants"))
    in
    List.fold_left make_node root decls
  in

  (* make a new call tree branch with the given root while evaluating constants *)
  let rec make_branch_constants root constants gconsts decls =
    let make_node (parent,constants) = function
        Function(func, def) -> (Func(func, def, parent), constants)
      | Constant(id, def) -> (
          let tmpfunc = Func({fname = id; fparams = []; locals = []}, def, parent) in
          let (path, expr) = build_call tmpfunc [] [] gconsts constants in
          let (v,u) = eval gconsts path expr in
          (parent, StringMap.add id (v,u) constants) )
      | _ -> raise(Failure("Can only nest definitions and constants"))
    in
    List.fold_left make_node (root,constants) decls

  (* create a call to a function *)
  and build_call node fnodes args gconsts baseconsts = 
    let (func, def) = match node with
        Func(func,def,_) -> (func,def)
      | _ -> raise( Failure("must build call with Func node"))
    in
    let (decls, expr) = match def with
        Single(expr) -> [], expr
      | Composite(decls, expr) -> decls, expr
      | None -> raise( LibCall)
    in
    let fbinds = List.combine (List.map (fun (s,_,_) -> s) func.fparams) fnodes in
    let binds = try List.combine func.locals args with
      | Invalid_argument(s) -> raise( Failure("wrong number of arguments"))
    in
    let (call_path,constants) = make_branch_constants (Fcall(fbinds,binds,StringMap.empty,node)) baseconsts gconsts decls in
    let call_path = if StringMap.is_empty constants then call_path else make_branch (Fcall(fbinds,binds,constants,node)) decls in
    call_path, expr

  (* evaluate an expression *)
  and eval constants call_path = 
    let float_of_bool b = if b then 1. else 0. in
    function
      FloatLit(l) -> l, false
  
    | Binop(e1, op, e2) -> (
        match op with
          | Div -> (* eval denominator first *)
              (let (v2, u2) = eval constants call_path e2 in
              if v2 = 0. then 0., true else
              let (v1, u1) = eval constants call_path e1 in
              v1 /. v2, u1 || u2)

          (* short circuits *)
          | Mult -> 
              (let (v1, u1) = eval constants call_path e1 in
              if v1 = 0. then v1, u1 else 
              let (v2, u2) = eval constants call_path e2 in
              v1 *. v2, u1 || u2 )
          | And -> 
              (let (v1, u1) = eval constants call_path e1 in
              if v1 = 0. then v1, u1 else
              let (v2, u2) = eval constants call_path e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Or -> 
              (let (v1, u1) = eval constants call_path e1 in
              if v1 <> 0. then 1., u1 else
              let (v2, u2) = eval constants call_path e2 in
              float_of_bool(v2 <> 0.), u1 || u2 )
          | Part -> 
              (let (v1,u1) = eval constants call_path e1 in
              if u1 then eval constants call_path e2 else v1, u1 )
          
          (* eval both sides for all cases *)
          | Add -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              v1 +. v2, u1 || u2 )
          | Sub -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              v1 -. v2, u1 || u2 )
          | Exp -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              v1 ** v2, if ((v1<0. && fst(modf v2)<>0.) || (v1=0. && v2=0.)) 
                        then true else u1 || u2 )
          | Equal -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 = v2), u1 || u2 )
          | Neq -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 <> v2), u1 || u2 )
          | Less -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 < v2), u1 || u2 )
          | Leq -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 <= v2), u1 || u2 )
          | Greater -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 > v2), u1 || u2 )
          | Geq -> 
              (let (v1, u1) = eval constants call_path e1 
              and (v2, u2) = eval constants call_path e2 in
              float_of_bool(v1 >= v2), u1 || u2 ) )
              

    | Unop(uop, e) ->
        (let (v,u) = eval constants call_path e in
        match uop with
            Neg -> ~-. v, u
          | Not -> float_of_bool(v = 0.), u )

    | Var(id) -> (
        try path_find_value call_path id with
        | Not_found -> try StringMap.find id constants with
        | Not_found -> 
            let node = (
              try (path_find_func call_path id) with
              | Not_found -> raise( Failure("unknown identifier " ^ id)) )
            in
            match node with
              Func(func,_,_) -> (match (func.fparams, func.locals) with
                ([],[]) -> (try (
                  let (call,expr) = build_call node [] [] constants StringMap.empty in
                  eval constants call expr ) with
                  | LibCall -> lib_eval id [])
                | _ -> raise( Failure("not enough arguments for " ^ id))
                )
              | _ -> raise( Failure("call node must be of type Func")) )

    | Call(id,fargs,args) -> (
        let node = (
          try (path_find_func call_path id) with
          | Not_found -> raise( Failure("cannot call " ^ id)) )
        in
        let fnodes = 
          let node_map = path_find call_path fargs StringMap.empty in
          let fsigs = match node with
              Func(func,_,_) -> func.fparams
            | _ -> raise( Failure("call node must be of type Func"))
          in
          let find_node farg fsig = 
            let nde = try StringMap.find farg node_map with
              | Not_found -> raise( Failure("cannot find function argument " ^ farg))
            in
            let func = match nde with
                Func(func,_,_) -> func
              | _ -> raise( Failure("function argument node must be of type Func"))
            in
            let (s,i1,i2) = fsig in
            if (List.length func.fparams = i1 && List.length func.locals = i2) 
            then nde else raise( Failure(farg ^ " has wrong function signature"))
          in
          try (List.map2 find_node fargs fsigs) with
            | Invalid_argument(s) -> raise ( Failure("wrong number of function arguments for " ^ id))
        in
        let lcls = List.map (fun e -> eval constants call_path e) args in
        try (
          let (call, expr) = build_call node fnodes lcls constants StringMap.empty in
          eval constants call expr ) with 
          | LibCall -> lib_eval id lcls )
  in

  (* parse a global statement *)
  let parse_global (globals, consts) = function
      | Function(func,def) -> (Func(func, def, globals), consts)
      | Constant(name,def) -> (
          let tmpfunc = Func({fname = name; fparams = []; locals = []}, def, globals) in
          let (path, expr) = build_call tmpfunc [] [] consts StringMap.empty in
          let (v,u) = eval consts path expr in
          (globals, StringMap.add name (v,u) consts) )
      | Expression(expr) -> (
          let dims = []
            (*let dim k (start,stop,step) l = 
              truncate ((stop -. start) /. step) :: l
            in
            StringMap.fold (dim) vars []*)
          in
          
          (*let inputs, names = generate_inputs vars in
          let solve input = 
            let add_from_lists = (fun m k v -> StringMap.add k (v,false) m) in
            let tmpconsts = List.fold_left2 (add_from_lists) consts names (input) in
            List.map (eval tmpconsts globals) exprs 
          in*)
          
          let print_tuple tuple = 
            let values = List.map (fst) tuple in
            let undefs = List.map (snd) tuple in
            let outputs = List.map (string_of_float) values in
            let is_undef = List.fold_left (||) false undefs in
            if is_undef then print_endline "undefined" 
            else print_endline (String.concat ", " outputs);
          in

          (*let results = List.map (solve) inputs in *)
          let results = List.map (eval consts globals) [expr] in
          if List.length dims = 0 then print_tuple results
          else print_endline (String.concat " " (List.map (string_of_int) dims));
          (globals, consts) )
      | Import(file) -> (
          let import = file ^ ".klib" in
          try (
            let ic = open_in import in 
            let lexbuf = Lexing.from_channel ic in
            let ast = Parser.program Scanner.token lexbuf in
            translate globals consts ast) 
          with
          | Sys_error(_) -> print_endline ("cannot use file " ^ file); 
          (globals, consts) )
  in

  List.fold_left parse_global (globals, consts) ast
