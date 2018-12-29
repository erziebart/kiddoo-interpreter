open Ast

module StringMap = Map.Make(String)

(* call tree types *)
type closure = {
  e: expr;
  mutable consts: (string list * closure) list;
  mutable calls: (fundata * int)StringMap.t
}

and fundata = sigture list * string list * closure

type ctree = 
  | Root
  | Fundecl of string * fundata * int * ctree
  | Condecl of string list * closure * int * ctree

(* when a function is found but pointer cannot be returned *)
exception Found

(* checks a single stmt and adds it to the call tree *)
let rec check_stmt depth (calltree,constants) = 

  (* helper functions to search for function or constant ids *)
  let rec find_value depth name = function
    | Fundecl(_,(_,args,_),d,p) -> 
        if d<depth && List.mem name args then true else find_value d name p
    | Condecl(names,_,d,p) -> 
        if List.exists ((=) name) names then true else find_value d name p
    | Root -> false
  in
  let rec find_func depth id = function
    | Fundecl(name,fundecl,d,p) -> let (fargs,_,_) = fundecl in
        if (d<depth && List.exists (fun (n,_,_) -> n=id) fargs) then raise(Found) else
          if (name=id) then (fundecl,d) else find_func d id p
    | Condecl(_,_,d,p) -> find_func d id p
    | Root -> raise(Not_found)
  in

  (* finds a function and adds it to a stringmap -- used on function arguments *)
  let find_and_add calltree map id = try StringMap.add id (find_func (depth+1) id calltree) map with
    | Found -> map
    | Not_found -> raise(Failure("unknown function argument "^id))
  in

  (* semantic check on an expression *)
  let rec check_expr calltree funptrs = function
    | Binop(e1,_,e2) -> check_expr calltree (check_expr calltree funptrs e1) e2
    | Unop(_,e) -> check_expr calltree funptrs e
    | Var(id) -> if find_value (depth+1) id calltree then funptrs else raise(Failure("unknown variable "^id))
    | Call(id,fargs,args) -> (
        try (
          let fdecl,d = find_func (depth+1) id calltree in
          let (far,ar,_) = fdecl in
          let farlen = List.length far and arlen = List.length ar in
          if compare farlen (List.length fargs) = 0 then
            (* if compare arlen (List.length args) = 0 then  *)
              let funptrs = check_expr calltree funptrs args in
              let funptrs = List.fold_left (find_and_add calltree) funptrs fargs in
              StringMap.add id (fdecl,d) funptrs
            (* else
              raise(Failure("wrong number of arguments passed to "^id^", expected "^string_of_int farlen)) *)
          else
            raise(Failure("wrong number of function arguments passed to "^id^", expected "^string_of_int arlen)) )
        with
          | Found -> funptrs
          | Not_found -> raise(Failure("unknown function "^id)) )
    | Tuple(exprs) -> List.fold_left (check_expr calltree) funptrs exprs
    | _ -> funptrs
  in

  (* helper functions for construction call tree nodes *)
  let parse_def = function
      Single(expr) -> [], expr
    | Composite(decls, expr) -> decls, expr
    | None -> [], Null
  in
  let init_closure expr = {e = expr; consts = []; calls = StringMap.empty} in
  let parse_inner decls head close = 
    let (call_branch, constants) = List.fold_left (check_stmt (depth+1)) (head, []) decls
    in
    let funptrs = check_expr call_branch StringMap.empty close.e in
    close.consts <- List.rev constants; close.calls <- funptrs
  in

  (* check_stmt body *)
  function
  | Function(func,def) -> 
      let (decls,expr) = parse_def def in
      let close = init_closure expr in
      let head = Fundecl(func.fname,(func.fparams, func.locals, close),depth,calltree) in
      parse_inner decls head close; head, constants
  | Constant(names,def) ->
      let (decls,expr) = parse_def def in
      let close = init_closure expr in
      let head = Condecl(names,close,depth,calltree) in
      parse_inner decls head close; head, (names,close) :: constants
  | Expression(expr) ->
      let names = ["->"] in
      let close = init_closure expr in
      let head = Condecl(names,close,depth,calltree) in
      parse_inner [] head close; head, (names,close) :: constants
  | Import(file) ->
      let import = file ^ ".klib" in
      try (
        let ic = open_in import in 
        let lexbuf = Lexing.from_channel ic in
        let ast = Parser.program Scanner.token lexbuf in
        List.fold_left (check_stmt depth) (calltree,constants) ast )
      with
      | Sys_error(_) -> print_endline ("cannot use file " ^ file); calltree, constants

(* for testing purposes *)
(*let _ = 

  let string_of_closure close = close.name ^ " calls: " ^ String.concat " " (List.map (fst) (StringMap.bindings close.calls)) in

  let string_of_ctree_decl = function
    | Decl(Fundecl(_,_,close),_,_) -> string_of_closure close
    | Decl(Condecl(close),_,_) -> string_of_closure close
    | Root -> raise(Failure("Whoops!"))
  in

  try
    let infile = Sys.argv.(1) in
    let ic = open_in infile in
    let lexbuf = Lexing.from_channel ic in
    let ast = Parser.program Scanner.token lexbuf in
    let check_and_print (calltree,constants) decl = 
      let (ctree_leaf, consts) = check_stmt 0 (calltree,constants) decl in
      print_endline (string_of_ctree_decl ctree_leaf); ctree_leaf,consts
    in
    ignore (List.fold_left check_and_print (Root,[]) ast)
  with 
    | Failure(s) -> print_endline s; exit 0 
    | Sys_error(s) -> print_endline s; exit 0
*)
