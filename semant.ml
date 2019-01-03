open Ast

module StringMap = Map.Make(String)

(* call tree types *)
(* type closure = {
  mutable consts: condata list;
  mutable calls: fundata StringMap.t
} *)

(* type fundata = {
  name: string;
  fparams: sigture list;
  params: string list;
  e: expr;
  mutable fconsts: condata list;
  mutable fcalls: fundata StringMap.t;
  depth: int;
}
and condata = {
  names: string list;
  exprs: expr list;
  mutable consts: condata list;
  mutable calls: fundata StringMap.t;
} *)

type ctree = 
  | Root
  | Fundecl of fundata * ctree
  | Condecl of condata * int * ctree

(* when a function is found but pointer cannot be returned *)
exception Found

(* checks a single stmt and adds it to the call tree *)
let rec check_stmt depth (calltree,constants) = 

  (* helper functions to search for function or constant ids *)
  let rec find_value depth name = function
    | Fundecl(data,p) -> 
        if data.depth<depth && List.mem name data.locals then true else find_value data.depth name p
    | Condecl(data,d,p) -> 
        if List.exists ((=) name) data.names then true else find_value d name p
    | Root -> false
  in
  let rec find_func depth id = function
    | Fundecl(data,p) ->
        if (data.depth<depth && List.exists (fun (n,_,_) -> n=id) data.flocals) then raise(Found) else
          if (data.name=id) then data else find_func data.depth id p
    | Condecl(data,d,p) -> find_func d id p
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
          let fdata = find_func (depth+1) id calltree in
          let farlen = List.length fdata.flocals and arlen = List.length fdata.locals in
          if compare farlen (List.length fargs) = 0 then
            if compare arlen (List.length args) = 0 || arlen = 1 then
              let funptrs = List.fold_left (check_expr calltree) funptrs args in
              let funptrs = List.fold_left (find_and_add calltree) funptrs fargs in
              StringMap.add id fdata funptrs
            else
              raise(Failure("wrong number of arguments passed to "^id^", expected "^string_of_int farlen))
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
      Single(exprs) -> [], exprs
    | Composite(decls, exprs) -> decls, exprs
    | None -> [], []
  in
(*   let init_closure = {consts = []; calls = StringMap.empty} in *)
  let init_func func expr = {
    name=func.fname; 
    flocals=func.fparams; 
    locals=func.params; 
    e=expr; 
    fconsts=[]; 
    fcalls=StringMap.empty; 
    depth=depth
  } 
  in
  let init_const names exprs = 
    let nl = List.length names and el = List.length exprs in
    if nl = 1 || el = 1 || nl = el then
      {
        names=names;
        exprs=exprs;
        consts=[];
        calls=StringMap.empty;
      }  
    else raise(Failure("incompatible constant assignment: " 
      ^ (string_of_int nl) ^ "!=" ^ (string_of_int el)))
  in

(*   let parse_inner_func decls head data = 
    let (call_branch, constants) = List.fold_left (check_stmt (depth+1)) (head, []) decls
    in
    let funptrs = check_expr call_branch StringMap.empty close.e in
    close.consts <- List.rev constants; close.calls <- funptrs
  in *)

  (* check_stmt body *)
  function
  | Function(func,def) -> (
      let (decls,exprs) = parse_def def in
      let expr = if List.length exprs = 1 then List.hd exprs else Tuple(exprs) in
      let data = init_func func expr in
      let head = Fundecl(data, calltree) in
      let (call_branch, consts) = List.fold_left (check_stmt (depth+1)) (head, []) decls in
      let funptrs = check_expr call_branch StringMap.empty expr in
      data.fconsts <- List.rev consts; data.fcalls <- funptrs;
      head, constants )
  | Constant(names,def) -> (
      let (decls,exprs) = parse_def def in
      let data = init_const names exprs in
      let head = Condecl(data,depth,calltree) in
      let (call_branch, consts) = List.fold_left (check_stmt (depth+1)) (head, []) decls in
      let funptrs = List.fold_left (check_expr call_branch) StringMap.empty exprs in
      data.consts <- List.rev consts; data.calls <- funptrs;
      head, data :: constants )
  | Expression(exprs) -> (
      let names = ["->"] in
      let data = init_const names exprs in
      let head = Condecl(data,depth,calltree) in
      let funptrs = List.fold_left (check_expr head) StringMap.empty exprs in
      data.calls <- funptrs;
      head, data :: constants )
  | Import(file) -> (
      let import = file ^ ".klib" in
      try (
        let ic = open_in import in 
        let lexbuf = Lexing.from_channel ic in
        let ast = Parser.program Scanner.token lexbuf in
        List.fold_left (check_stmt depth) (calltree,constants) ast )
      with
      | Sys_error(_) -> print_endline ("cannot use file " ^ file); calltree, constants )

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
