%{ 
  open Ast

  let simplify_tuple = function
    | [expr] -> expr
    | tuple -> Tuple(List.rev tuple)
%}

%token PLUS MINUS TIMES DIVIDE POWER
%token EQ NEQ LT GT LEQ GEQ
%token AND OR NOT
%token SEMI
%token DEFINE CONST USE ASSIGN ARROW
%token LPAREN RPAREN LBRACE RBRACE COMMA
%token LIB
%token <string> ID FID FFID
%token <int> INTLIT
%token <float> FLTLIT
%token EOF

%left COMMA
%left SEMI
%left OR
%left AND
%left EQ NEQ
%left LT GT LEQ GEQ
%left PLUS MINUS
%left TIMES DIVIDE
%right NOT NEG
%right POWER

%start program
%type <Ast.program> program

%%

program:
    top_decl_list EOF { List.rev($1) }

top_decl_list:
    /* nothing */ { [] }
  | top_decl_list top_decl { $2 :: $1 }

top_decl:
    DEFINE func ASSIGN def { Function($2, $4) }
  | LIB DEFINE func { Function($3, None) }
  | CONST id_list ASSIGN def { Constant(List.rev $2, $4) }
  | ARROW tuple { Expression(List.rev $2) }
  | USE ID { Import($2) }

decl_list:
    /* nothing */ { [] }
  | decl_list decl { $2 :: $1 }

decl:
    DEFINE func ASSIGN def { Function($2, $4) }
  | CONST id_list ASSIGN def { Constant(List.rev $2, $4) }
  | LIB DEFINE func { Function($3, None) }

func:
    ID { { fname = $1; fparams = []; locals = [] } }
  | FID formals_opt RPAREN { { fname = $1; fparams = []; locals = List.rev($2) } }
  | FFID formal_funcs RBRACE LPAREN formals_opt RPAREN { { fname = $1; fparams = List.rev($2); locals = List.rev($5) } }
  | FID formals_opt RPAREN LBRACE formal_funcs RBRACE { { fname = $1; fparams = List.rev($5); locals = List.rev($2) } }

def:
    decl_list ARROW tuple { Composite(List.rev($1), List.rev $3) }
  | tuple { Single(List.rev $1) }

tuple:
    expr { [$1] }
  | tuple COMMA expr { $3 :: $1 }

expr:
    expr SEMI expr { Binop($1, Part, $3) } 
  | expr OR expr { Binop($1, Or, $3) }
  | expr AND expr {Binop($1, And, $3) }
  | expr LT expr { Binop($1, Less, $3) }
  | expr LEQ expr { Binop($1, Leq, $3) }
  | expr GT expr { Binop($1, Greater, $3) } 
  | expr GEQ expr { Binop($1, Geq, $3) }
  | expr EQ expr { Binop($1, Equal, $3) }
  | expr NEQ expr { Binop($1, Neq, $3) }
  | expr PLUS term { Binop($1, Add, $3) }
  | expr MINUS term { Binop($1, Sub, $3) } 
  | term { $1 }

term:
    term TIMES factor { Binop($1, Mult, $3) } 
  | term noneg_factor %prec TIMES { Binop($1, Mult, $2) } 
  | term DIVIDE factor { Binop($3, Div, $1) }
  | factor { $1 }

factor:
    value POWER factor { Binop($1, Exp, $3) }
  | MINUS factor %prec NEG { Unop(Neg, $2) }
  | NOT factor { Unop(Not, $2) }
  | value { $1 }

noneg_factor:
    value POWER factor { Binop($1, Exp, $3) }
  | NOT factor { Unop(Not, $2) }
  | value { $1 }

value:
    INTLIT { IntLit($1) }
  | FLTLIT { FloatLit($1) }
  | call { $1 } 
  | LPAREN tuple RPAREN { simplify_tuple $2 } 

call:
    ID { Var($1) }
  | FID actuals_opt RPAREN { Call($1, [], $2) } 
  | FFID id_list RBRACE LPAREN actuals_opt RPAREN { Call($1, List.rev($2), $5) } 
  | FID actuals_opt RPAREN LBRACE id_list RBRACE { Call($1, List.rev($5), $2) }
 
formals_opt: 
    /* nothing */ { [] }
  | id_list       { $1 }

id_list:
    ID { [$1] }
  | id_list COMMA ID { $3 :: $1 }

formal_funcs:
    ID LT INTLIT INTLIT GT { [($1, $3, $4)] }
  | formal_funcs COMMA ID LT INTLIT INTLIT GT { ($3, $5, $6) :: $1 }

actuals_opt:
    /* nothing */ { [] } 
  | tuple { List.rev($1) }
