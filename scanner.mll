{ 
  open Parser 
  (*exception Eof*)
}

rule token = parse
    [' ' '\t' '\r' '\n'] { token lexbuf } (* Whitespace *)
  | "{*"                 { multi 0 lexbuf } (* Nested multi-Line Comments *)
  | '+'                  { PLUS }
  | '-'                  { MINUS }
  | '*'                  { TIMES }
  | '/'                  { DIVIDE }
  | '^'                  { POWER }
  | "def"                { DEFINE }
  | "con"                { CONST }
  | "var"                { VAR }
  | "use"                { USE }
  | '='                  { ASSIGN }
  | "->"                 { ARROW }
  | "=="                 { EQ }
  | "!="                 { NEQ }
  | '<'                  { LT }
  | '>'                  { GT }
  | "<="                 { LEQ }
  | ">="                 { GEQ }
  | '&'                  { AND }
  | '|'                  { OR }
  | '!'                  { NOT }
  | ';'                  { SEMI }
  | '('                  { LPAREN }
  | ')'                  { RPAREN }
  | '['                  { LBRACE }
  | ']'                  { RBRACE }
  | ','                  { COMMA }

  | "#lib"               { LIB }

  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm '(' { FID(lxm) }
  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm '[' { FFID(lxm) } 
  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { ID(lxm) }
  | ['0'-'9']*'.'['0'-'9']+ | ['0'-'9']+'.'['0'-'9']* as lxm { FLTLIT(float_of_string lxm) }
  | ['0'-'9']+ as lxm { INTLIT(int_of_string lxm) }
  
  | eof { EOF }
  | _ as char { raise (Failure("illegal character " ^ Char.escaped char)) }
   

and multi depth = parse
  | "{*"                 { multi (depth + 1) lexbuf }
  | "*}"                 { if depth = 0 then token lexbuf else multi (depth - 1) lexbuf }
  | _                    { multi depth lexbuf }
