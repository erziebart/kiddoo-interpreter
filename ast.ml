(* Abstract Syntax Tree *)
type op = Add | Sub | Mult | Div | Exp | Equal | Neq | Less | Leq | Greater | Geq | And | Or

type uop = Neg | Not

type expr = 
    FloatLit of float
  | Binop of expr * op * expr
  | Unop of uop * expr
  | Part of expr * expr
  | Var of string
  | Call of string * string list * expr list 

type sigture = string * int * int

type func = {
  fname: string;
  fparams: sigture list;
  locals: string list;
}

type decl = 
    Function of func * def
  | Constant of string * def
  | Variable of string * expr * expr * expr
  | Expression of expr list
  | Import of string
and def = 
    Composite of decl list * expr 
  | Single of expr
  | None

type program = decl list

(* Pretty-printing functions *)
let string_of_op = function
    Add -> "+"
  | Sub -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Exp -> "^"
  | Equal -> "=="
  | Neq -> "!="
  | Less -> "<"
  | Leq -> "<="
  | Greater -> ">"
  | Geq -> ">="
  | And -> "&"
  | Or -> "|"

let string_of_uop = function
    Neg -> "-"
  | Not -> "!"

let string_of_fargs = function
    [] -> ""
  | _ as f -> "[" ^ String.concat ", " f ^ "]"

let rec string_of_expr = function
    FloatLit(l) -> string_of_float l
  | Binop(e1, o, e2) -> "(" ^ string_of_expr e1 ^ " " ^ string_of_op o ^ " " ^ string_of_expr e2 ^ ")"
  | Unop(o, e) -> string_of_uop o ^ string_of_expr e
  | Part(e1, e2) -> string_of_expr e1 ^ " ; " ^ string_of_expr e2
  | Call(n, f, a) -> n ^ string_of_fargs f ^ "(" ^ String.concat ", " (List.map string_of_expr a) ^ ")"
  | Var(s) -> s

let string_of_sigture (id, l1, l2) = id ^ "<" ^ string_of_int l1 ^ " " ^ string_of_int l2 ^ ">"

let string_of_fparams = function
    [] -> ""
  | _ as l -> "[" ^ String.concat ", " (List.map string_of_sigture l) ^ "]"

let string_of_func func = func.fname ^ string_of_fparams func.fparams ^ "(" ^ String.concat ", " func.locals ^ ")"

let rec string_of_decl = function
    Function(func, def) -> "def " ^ string_of_func func ^ " = " ^ string_of_def def
  | Constant(id,def) -> "con " ^ id ^ " = " ^ string_of_def def
  | Variable(id,start,stop,step) -> "var " ^ id ^ " [" ^ string_of_expr start ^ "; " ^ string_of_expr stop ^ "; " ^ string_of_expr step ^ "]"
  | Expression(exprs) -> "-> " ^ String.concat ", " (List.map string_of_expr exprs)
  | Import(s) -> "use" ^ s
and string_of_def = function
    Single(e) -> string_of_expr e ^ "\n"
  | Composite(decls, e) -> "{\n" ^ String.concat "\n" (List.map string_of_decl decls) ^ "}\n" ^ string_of_expr e ^ "\n"
  | None -> "\n"

let string_of_program (decls) = String.concat "" (List.map (fun decl -> string_of_decl decl ^ "\n") decls) 
