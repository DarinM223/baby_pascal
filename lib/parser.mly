%token SEMI COLON EQUALS NEQUALS ASSIGN LPAREN RPAREN COMMA
%token PLUS MINUS TIMES NOT AND OR LT LE GT GE
%token VAR
%token TRUE FALSE
%token FUNCTION PROCEDURE BEGIN END IF THEN ELSE WHILE DO
%token INTEGER BOOLEAN VOID
%token<string> IDENT
%token<int> INT
%token EOF

%left AND OR
%left EQUALS NEQUALS
%left LT LE GT GE
%left PLUS MINUS
%left TIMES
%nonassoc NOT

%start <Ast.stmt Ast.program> program
%type <string * Ast.typ> global
%type <Ast.typ> typ
%type <Ast.stmt Ast.decl> decl
%type <Ast.stmt> statement
%type <Ast.expr> expr

%%

program:
| g = global SEMI p = program {{ p with globals = p.Ast.globals @ [g] }}
| d = decl p = program {{ p with decls = p.Ast.decls @ [d] }}
| main = statement p = program {{ p with main }}
| EOF {{ Ast.globals = []; decls = []; main = Ast.Group [] }}

global:
| VAR r = separated_pair(IDENT, COLON, typ) {r}

typ:
| LPAREN params = separated_list(COMMA, typ) RPAREN COLON ret = typ {Ast.TFunction (params, Some ret)}
| INTEGER {Ast.TInteger}
| BOOLEAN {Ast.TBoolean}
| VOID {Ast.TVoid}

decl:
| FUNCTION i = IDENT LPAREN params = separated_list(COMMA, separated_pair(IDENT, COLON, typ))
  RPAREN COLON ret = typ SEMI stmt = statement
  {Ast.Function (i, params, ret, stmt)}
| PROCEDURE i = IDENT LPAREN params = separated_list(COMMA, separated_pair(IDENT, COLON, typ))
  RPAREN SEMI stmt = statement
  {Ast.Procedure (i, params, stmt)}

statement:
| BEGIN stmts = list(terminated(statement, SEMI)) END {Ast.Group stmts}
| IF e = expr THEN thn = statement {Ast.If (e, thn, Group [])}
| IF e = expr THEN thn = statement ELSE els = statement {Ast.If (e, thn, els)}
| WHILE e = expr DO body = statement {Ast.While (e, body)}
| i = IDENT ASSIGN e = expr {Ast.Assign (i, e)}
| f = IDENT LPAREN exprs = separated_list(COMMA, expr) RPAREN {Ast.Call (f, exprs)}

expr:
| NOT e = expr {Ast.Uop (Not, e)}
| lhs = expr EQUALS rhs = expr {Ast.Bop (Eq, lhs, rhs)}
| lhs = expr NEQUALS rhs = expr {Ast.Bop (Neq, lhs, rhs)}
| lhs = expr GT rhs = expr {Ast.Bop (Gt, lhs, rhs)}
| lhs = expr GE rhs = expr {Ast.Bop (Ge, lhs, rhs)}
| lhs = expr LT rhs = expr {Ast.Bop (Lt, lhs, rhs)}
| lhs = expr LE rhs = expr {Ast.Bop (Le, lhs, rhs)}
| lhs = expr TIMES rhs = expr {Ast.Bop (Mul, lhs, rhs)}
| lhs = expr PLUS rhs = expr {Ast.Bop (Add, lhs, rhs)}
| lhs = expr MINUS rhs = expr {Ast.Bop (Sub, lhs, rhs)}
| lhs = expr AND rhs = expr {Ast.Bop (And, lhs, rhs)}
| lhs = expr OR rhs = expr {Ast.Bop (Or, lhs, rhs)}
| f = IDENT LPAREN exprs = separated_list(COMMA, expr) RPAREN {Ast.Call (f, exprs)}
| v = IDENT {Ast.Var v}
| TRUE {Ast.Bool true}
| FALSE {Ast.Bool false}
| i = INT {Ast.Int i}