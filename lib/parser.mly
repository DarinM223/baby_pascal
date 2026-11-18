%token SEMI COLON EQUALS NEQUALS ASSIGN LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE COMMA DOT AMPER EXPONENT ATSIGN RECORD
%token PLUS MINUS TIMES DIV NOT AND OR LT LE GT GE
%token VAR TYPE
%token TRUE FALSE
%token FUNCTION PROCEDURE BEGIN END IF THEN ELSE WHILE DO ALLOCA
%token INT64 BOOLEAN VOID DOUBLE CHAR
%token<string> IDENT
%token<string> STRING
%token<int> INT
%token<float> FLOAT
%token<char> CHAR_LIT
%token EOF

%left AND OR
%left EQUALS NEQUALS
%left LT LE GT GE
%left PLUS MINUS
%left TIMES DIV
%nonassoc NOT

%start <Ast.stmt Ast.program> program
%type <Ast.global_def list> global
%type <(string * Ast.typ) list> binding
%type <Ast.typ> typ
%type <unit> typ_decls
%type <unit> typ_binding
%type <Ast.stmt Ast.decl> decl
%type <Ast.stmt> statement
%type <Ast.expr> expr
%type <Ast.expr> lvalue

%%

program:
| t = typ_decls p = program {p}
| g = global p = program {{ p with globals = p.Ast.globals @ g }}
| d = decl p = program {{ p with decls = p.Ast.decls @ [d] }}
| BEGIN main = list(terminated(statement, SEMI)) END p = program {{ p with main = Ast.Group main }}
| EOF {{ Ast.globals = []; decls = []; main = Ast.Group [] }}

typ_decls:
| TYPE r = nonempty_list(terminated(typ_binding, SEMI)) {()}

typ_binding:
| id = IDENT EQUALS ty = typ {Ast.(SymbolTable.add alias_table id ty)}

global:
| VAR r = nonempty_list(terminated(binding, SEMI))
  {List.concat_map (List.map (fun (id, typ) -> { Ast.id; typ; value = Ast.External })) r}

binding:
| r = separated_pair(separated_nonempty_list(COMMA, IDENT), COLON, typ)
  {let ids, typ = r in List.map (fun id -> (id, typ)) ids}

typ:
| LPAREN params = separated_list(COMMA, typ) RPAREN COLON ret = typ {Ast.TFunction (params, Some ret)}
| LBRACK size = INT RBRACK t = typ {Ast.TArray (t, size)}
| RECORD fields = list(terminated(separated_pair(IDENT, COLON, typ), SEMI)) END {Ast.TRecord fields}
| INT64 {Ast.TInteger64}
| BOOLEAN {Ast.TBoolean}
| DOUBLE {Ast.TDouble}
| VOID {Ast.TVoid}
| CHAR {Ast.TChar}
| EXPONENT t = typ {Ast.TPointer t}
| id = IDENT
  {
  match Ast.(SymbolTable.find_opt alias_table id) with
  | Some typ -> typ
  | None -> raise @@ Utils.Parser_error (Format.asprintf "unknown type alias %s" id)
  }

decl:
| FUNCTION i = IDENT LPAREN params = separated_list(COMMA, separated_pair(IDENT, COLON, typ))
  RPAREN COLON ret = typ SEMI stmt = statement
  {Ast.Function (i, params, ret, stmt)}
| PROCEDURE i = IDENT LPAREN params = separated_list(COMMA, separated_pair(IDENT, COLON, typ))
  RPAREN SEMI stmt = statement
  {Ast.Procedure (i, params, stmt)}

statement:
| BEGIN stmts = list(terminated(statement, SEMI)) END {Ast.Group stmts}
| VAR r = separated_pair(separated_nonempty_list(COMMA, IDENT), COLON, typ)
  {let (ids, typ) = r in Ast.Group (List.map (fun id -> Ast.Declare (id, typ)) ids)}
| IF e = expr THEN thn = statement {Ast.If (e, thn, Group [])}
| IF e = expr THEN thn = statement ELSE els = statement {Ast.If (e, thn, els)}
| WHILE e = expr DO body = statement {Ast.While (e, body)}
| e1 = lvalue ASSIGN rv = rvalue
  {
  match e1, rv with
  | Ast.Var v, `Alloca (t, i) -> Ast.Alloca (v, t, i)
  | _, `Exp e2 -> Ast.Assign (e1, e2)
  | _ -> raise (Utils.Parser_error "invalid assignment statement")
  }
| f = IDENT LPAREN exprs = separated_list(COMMA, expr) RPAREN {Ast.Call (f, exprs)}

lvalue:
| id = IDENT {Ast.Var id}
| e1 = lvalue LBRACK e2 = expr RBRACK {Ast.ArrayIndex (e1, e2)}
| e1 = lvalue DOT field = IDENT {Ast.RecordField (e1, field)}
| e = lvalue EXPONENT {Ast.Deref e}

rvalue:
| ALLOCA t = typ i = INT {`Alloca (t, i)}
| e = expr {`Exp e}

expr:
| LPAREN e = expr RPAREN {e}
| ATSIGN e = expr {Ast.Addrof e}
| e = expr EXPONENT {Ast.Deref e}
| LBRACK init = expr SEMI size = INT RBRACK {Ast.Array (init, size)}
| lhs = expr LBRACK rhs = expr RBRACK {Ast.ArrayIndex (lhs, rhs)}
| lhs = expr DOT rhs = IDENT {Ast.RecordField (lhs, rhs)}
| NOT e = expr {Ast.Uop (Not, e)}
| lhs = expr EQUALS rhs = expr {Ast.Bop (Eq, lhs, rhs)}
| lhs = expr NEQUALS rhs = expr {Ast.Bop (Neq, lhs, rhs)}
| lhs = expr GT rhs = expr {Ast.Bop (Gt, lhs, rhs)}
| lhs = expr GE rhs = expr {Ast.Bop (Ge, lhs, rhs)}
| lhs = expr LT rhs = expr {Ast.Bop (Lt, lhs, rhs)}
| lhs = expr LE rhs = expr {Ast.Bop (Le, lhs, rhs)}
| lhs = expr TIMES rhs = expr {Ast.Bop (Mul, lhs, rhs)}
| lhs = expr DIV rhs = expr {Ast.Bop (Div, lhs, rhs)}
| lhs = expr PLUS rhs = expr {Ast.Bop (Add, lhs, rhs)}
| lhs = expr MINUS rhs = expr {Ast.Bop (Sub, lhs, rhs)}
| lhs = expr AND rhs = expr {Ast.Bop (And, lhs, rhs)}
| lhs = expr OR rhs = expr {Ast.Bop (Or, lhs, rhs)}
| f = IDENT LPAREN exprs = separated_list(COMMA, expr) RPAREN {Ast.Call (f, exprs)}
| v = IDENT {Ast.Var v}
| TRUE {Ast.Bool true}
| FALSE {Ast.Bool false}
| f = FLOAT {Ast.Double f}
| c = CHAR_LIT {Ast.Char c}
| i = INT {Ast.Int i}
| s = STRING {Ast.String s}