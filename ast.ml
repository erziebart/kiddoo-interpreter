(* Abstract Syntax Tree *)
type op = Add | Sub | Mult | Div | Idiv | Mod | Exp | Equal | Neq | Less | Leq | Greater | Geq | And | Or | Part

type uop = Neg | Not

type expr = 
    FloatLit of float
  | IntLit of int
  | Binop of expr * op * expr
  | Unop of uop * expr
  | Var of string
  | Call of string * string list * expr list
  | Tuple of expr list
  | Set of item list
and item = 
    Element of expr
  | Range of range
and opt_expr = 
    Expr of expr
  | None
and range = {
  start: opt_expr;
  stop: opt_expr;
  step: opt_expr;
}

type sigture = string * int * int

type func = {
  fname: string;
  fparams: sigture list;
  locals: string list;
}

type decl = 
    Function of func * def
  | Constant of string list * def
  | Expression of expr list 
  | Import of string
and def = 
    Composite of decl list * expr list
  | Single of expr list
  | None

type program = decl list

(* Pretty-printing functions *)
let string_of_op = function
    Add -> "+"
  | Sub -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Idiv -> "//"
  | Mod -> "%"
  | Exp -> "^"
  | Equal -> "=="
  | Neq -> "!="
  | Less -> "<"
  | Leq -> "<="
  | Greater -> ">"
  | Geq -> ">="
  | And -> "&"
  | Or -> "|"
  | Part -> ";"

let string_of_uop = function
    Neg -> "-"
  | Not -> "!"

let string_of_fargs = function
    [] -> ""
  | _ as f -> "[" ^ String.concat ", " f ^ "]"

let rec string_of_expr = function
    FloatLit(l) -> string_of_float l
  | IntLit(i) -> string_of_int i
  | Binop(e1, o, e2) -> "(" ^ string_of_expr e1 ^ " " ^ string_of_op o ^ " " ^ string_of_expr e2 ^ ")"
  | Unop(o, e) -> string_of_uop o ^ string_of_expr e
  | Call(n, f, a) -> n ^ string_of_fargs f ^ "(" ^ string_of_tuple a ^ ")"
  | Var(s) -> s
  | Tuple(exprs) -> string_of_tuple exprs
  | Set(items) -> "[" ^ String.concat ", " (List.map string_of_set_item items) ^ "]"
and string_of_tuple exprs = String.concat ", " (List.map string_of_expr exprs)
and string_of_set_item = function
    Element(expr) -> string_of_expr expr
  | Range(range) -> string_of_opt_expr range.start ^ ": " ^ string_of_opt_expr range.stop ^ ": " ^ string_of_opt_expr range.step
and string_of_opt_expr = function
    Expr(e) -> string_of_expr e
  | None -> ""

let string_of_sigture (id, l1, l2) = id ^ "<" ^ string_of_int l1 ^ " " ^ string_of_int l2 ^ ">"

let string_of_fparams = function
    [] -> ""
  | _ as l -> "[" ^ String.concat ", " (List.map string_of_sigture l) ^ "]"

let string_of_func func = func.fname ^ string_of_fparams func.fparams ^ "(" ^ String.concat ", " func.locals ^ ")"

let rec string_of_decl = function
    Function(func, def) -> "def " ^ string_of_func func ^ " = " ^ string_of_def def
  | Constant(ids,def) -> "con " ^ String.concat ", " ids ^ " = " ^ string_of_def def
  | Expression(exprs) -> string_of_tuple exprs
  | Import(s) -> "use" ^ s
and string_of_def = function
    Single(exprs) -> string_of_tuple exprs ^ "\n"
  | Composite(decls, exprs) -> "{\n" ^ String.concat "\n" (List.map string_of_decl decls) ^ "}\n" ^ string_of_tuple exprs ^ "\n"
  | None -> "\n"

let string_of_program (decls) = String.concat "" (List.map (fun decl -> string_of_decl decl ^ "\n") decls) 
