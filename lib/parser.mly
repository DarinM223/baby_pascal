%token SEMI COLON EQUALS ASSIGN LPAREN RPAREN
%token PLUS MINUS TIMES
%token VAR
%token INTEGER BOOLEAN VOID
%token<string> IDENT
%token<int> INT
%token EOF

%start <Ast.program> program
%type <string * Ast.typ> global
%type <Ast.typ> typ
// %type <Ast.decl> decl
// %type <Ast.stmt list> statements

%%

program:
| g = global SEMI p = program { { p with globals = p.Ast.globals @ [g] }}
| EOF { {Ast.globals = []; decls = []; main = []} }

global:
| VAR i = IDENT COLON {i, Ast.TInteger}

typ:
| INTEGER {Ast.TInteger}
| BOOLEAN {Ast.TBoolean}
| VOID {Ast.TVoid}
// | LPAREN (param = typ) RPAREN COLON (ret = typ) =

// decl:

// statements:
