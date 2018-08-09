open Ast

module StringMap = Map.Make(String)

(* call tree types *)
type closure = {
  name: string;
  e: expr;
  mutable consts: closure list;
  mutable calls: (metadata * int)StringMap.t
}

and metadata = 
  | Fundecl of sigture list * string list * closure
  | Condecl of closure

type ctree = 
  | Root
  | Decl of metadata * int * ctree

(* when a function is found but pointer cannot be returned *)
exception Found

(* checks a single stmt and adds it to the call tree *)
let rec check_stmt depth calltree = 

  (* helper functions to search for function or constant ids *)
  let rec find_value depth name = function
    | Decl(Fundecl(_,args,_),d,p) -> 
        if d<depth && List.mem name args then true else find_value d name p
    | Decl(Condecl(close),d,p) -> 
        if close.name=name then true else find_value d name p
    | Root -> false
  in
  let rec find_func depth id = function
    | Decl(Fundecl(fargs,_,close) as fundecl,d,p) -> 
        if (d<depth && List.exists (fun (n,_,_) -> n=id) fargs) then raise(Found) else
          if (close.name=id) then (fundecl,d) else find_func d id p
    | Decl(Condecl(_),d,p) -> find_func d id p
    | Root -> raise(Not_found)
  in

  (* semantic check on an expression *)
  let rec check_expr calltree funptrs = function
    | Binop(e1,_,e2) -> check_expr calltree (check_expr calltree funptrs e1) e2
    | Unop(_,e) -> check_expr calltree funptrs e
    | Var(id) -> if find_value depth id calltree then funptrs else raise(Failure("unknown variable "^id))
    | Call(id,fargs,args) -> (
        let funptrs = List.fold_left (check_expr calltree) funptrs args in
        try 
          let fdecl,d = find_func depth id calltree in
          match fdecl with
            | Fundecl(far,ar,_) -> (
                let farlen = List.length far and arlen = List.length ar in
                if compare farlen (List.length fargs) = 0 then
                  if compare arlen (List.length args) = 0 then 
                    StringMap.add id (fdecl,d) funptrs
                  else
                    raise(Failure("wrong number of function arguments passed to "^id^", expected "^string_of_int farlen))
                else
                  raise(Failure("wrong number of arguments passed to "^id^", expected "^string_of_int arlen)) )
            | _ -> raise(Failure("should have returned a function -- should not be thrown ever"))
        with
          | Found -> funptrs
          | Not_found -> raise(Failure("unknown function "^id)) )
    | _ -> funptrs
  in

  (* helper functions for construction call tree nodes *)
  let parse_def = function
      Single(expr) -> [], expr
    | Composite(decls, expr) -> decls, expr
    | None -> [], Null
  in
  let init_closure name expr = {name = name; e = expr; consts = []; calls = StringMap.empty} in
  let parse_inner decls head close = 
    let (call_branch, constants) = 
      let add_decl (branch, consts) decl = 
        let leaf = check_stmt (depth+1) branch decl in
        match leaf with
         | Decl(Fundecl(_,_,_),_,_) -> (leaf, consts)
         | Decl(Condecl(close),_,_) -> (leaf, close :: consts)
         | Root -> raise(Failure("check stmt should never produce Root"))
      in
      List.fold_left add_decl (head, []) decls
    in
    let funptrs = check_expr call_branch StringMap.empty close.e in
    close.consts <- constants; close.calls <- funptrs
  in

  function
  | Function(func,def) -> 
      let (decls,expr) = parse_def def in
      let close = init_closure func.fname expr in
      let head = Decl(Fundecl(func.fparams, func.locals, close),depth,calltree) in
      parse_inner decls head close; head
  | Constant(name,def) ->
      let (decls,expr) = parse_def def in
      let close = init_closure name expr in
      let head = Decl(Condecl(close),depth,calltree) in
      parse_inner decls head close; head
  | Expression(expr) ->
      let close = init_closure "->" expr in
      let head = Decl(Condecl(close),depth,calltree) in
      parse_inner [] head close; head
  | Import(file) -> raise(Failure("imports not yet implemented"))

