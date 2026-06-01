%token SEMI COLON EQUALS ASSIGN LPAREN RPAREN COMMA
%token PLUS MINUS TIMES
%token VAR
%token FUNCTION BEGIN END IF THEN ELSE
%token INTEGER BOOLEAN VOID
%token<string> IDENT
%token<int> INT
%token EOF

%start <Ast.program> program
%type <string * Ast.typ> global
%type <Ast.typ> typ
%type <Ast.decl> decl
%type <Ast.stmt> statement
%type <Ast.expr> expr

%%

program:
| g = global SEMI p = program { { p with globals = p.Ast.globals @ [g] }}
| d = decl p = program { { p with decls = p.Ast.decls @ [d] }}
| EOF { {Ast.globals = []; decls = []; main = Group []} }

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
| FUNCTION i = IDENT LPAREN params = separated_list(COMMA, separated_pair(IDENT, COLON, typ))
  RPAREN SEMI stmt = statement
  {Ast.Procedure (i, params, stmt)}

statement:
| stmts = delimited(BEGIN, list(terminated(statement, SEMI)), END) {Ast.Group stmts}
| IF e = expr THEN thn = statement ELSE els = statement {Ast.If (e, thn, els)}
| i = IDENT ASSIGN e = expr {Ast.Assign (i, e)}

expr:
| i = INT {Ast.Int i}