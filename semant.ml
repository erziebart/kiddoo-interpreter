open Ast
open Datatypes

module StringMap = Map.Make(String)

type fundata = {
  name: string;
  fparams: sigture list;
  params: string list;
  e: expr;
  mutable fconsts: condata list;
  mutable fcalls: fundata StringMap.t;
  mutable fnested: fundata list;
  mutable flocals: set StringMap.t;
  depth: int;
}
and condata = {
  names: string list;
  exprs: expr list;
  mutable consts: condata list;
  mutable calls: fundata StringMap.t;
  mutable nested: fundata list;
}

type ctree = 
  | Root
  | Fundecl of fundata * ctree
  | Condecl of condata * int * ctree

(* when a function is found but pointer cannot be returned *)
exception Found

(* checks a single stmt and adds it to the call tree *)
let rec check_stmt depth (calltree,constants,functions) = 

  (* helper functions to search for function or constant ids *)
  let rec find_value depth name = function
    | Fundecl(data,p) -> 
        if data.depth<depth && List.mem name data.params then true else find_value data.depth name p
    | Condecl(data,d,p) -> 
        if List.exists ((=) name) data.names then true else find_value d name p
    | Root -> false
  in
  let rec find_func depth id = function
    | Fundecl(data,p) ->
        if (data.depth<depth && List.exists (fun (n,_,_) -> n=id) data.fparams) then raise(Found) else
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
    | Access(e,exprs) -> List.fold_left (check_expr calltree) (check_expr calltree funptrs e) exprs
    | Call(id,fargs,args) -> (
        try (
          let fdata = find_func (depth+1) id calltree in
          let farlen = List.length fdata.fparams and arlen = List.length fdata.params in
          if Pervasives.compare farlen (List.length fargs) = 0 then
            if Pervasives.compare arlen (List.length args) = 0 || arlen = 1 then
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
    | Set(items) -> List.fold_left (check_set_item calltree) funptrs items
    | _ -> funptrs
  and check_set_item calltree funptrs = function
    | Element(expr) -> check_expr calltree funptrs expr
    | Range(range) -> (
        let check_opt funptrs = function
          | Expr(expr) -> check_expr calltree funptrs expr
          | None -> funptrs
        in
        let params = [range.start; range.stop; range.step] in
        List.fold_left check_opt funptrs params )
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
    fparams=func.fparams; 
    params=func.locals; 
    e=expr; 
    fconsts=[]; 
    fcalls=StringMap.empty; 
    fnested=[];
    flocals=StringMap.empty;
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
        nested=[];
      }  
    else raise(Failure("incompatible constant assignment: " 
      ^ (string_of_int nl) ^ "!=" ^ (string_of_int el)))
  in

  (* check_stmt body *)
  function
  | Function(func,def) -> (
      let (decls,exprs) = parse_def def in
      let expr = if List.length exprs = 1 then List.hd exprs else Tuple(exprs) in
      let data = init_func func expr in
      let head = Fundecl(data, calltree) in
      let (call_branch, consts, fns) = List.fold_left (check_stmt (depth+1)) (head, [], []) decls in
      let funptrs = check_expr call_branch StringMap.empty expr in
      data.fconsts <- List.rev consts; data.fcalls <- funptrs; data.fnested <- fns;
      head, constants, data :: functions )
  | Constant(names,def) -> (
      let (decls,exprs) = parse_def def in
      let data = init_const names exprs in
      let head = Condecl(data,depth,calltree) in
      let (call_branch, consts, fns) = List.fold_left (check_stmt (depth+1)) (head, [], []) decls in
      let funptrs = List.fold_left (check_expr call_branch) StringMap.empty exprs in
      data.consts <- List.rev consts; data.calls <- funptrs; data.nested <- fns;
      head, data :: constants, functions )
  | Expression(exprs) -> (
      let names = ["->"] in
      let data = init_const names exprs in
      let head = Condecl(data,depth,calltree) in
      let funptrs = List.fold_left (check_expr head) StringMap.empty exprs in
      data.calls <- funptrs;
      head, data :: constants, functions )
  | Import(file) -> (
      let import = file ^ ".klib" in
      try (
        let ic = open_in import in 
        let lexbuf = Lexing.from_channel ic in
        let ast = Parser.program Scanner.token lexbuf in
        List.fold_left (check_stmt depth) (calltree,constants,functions) ast )
      with
      | Sys_error(_) -> print_endline ("cannot use file " ^ file); calltree, constants, functions )
