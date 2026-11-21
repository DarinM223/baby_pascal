%token SEMI COLON EQUALS NEQUALS ASSIGN LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE COMMA DOT DOTDOT AMPER EXPONENT ATSIGN RECORD
%token PLUS MINUS TIMES DIV NOT AND OR LT LE GT GE
%token VAR TYPE
%token TRUE FALSE
%token FUNCTION PROCEDURE BEGIN END IF THEN ELSE WHILE DO ALLOCA OF
%token INT64 INT32 INT16 BOOLEAN VOID SINGLE DOUBLE CHAR ARRAY
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
%type <int * int> array_range
%type <Ast.typ> typ
%type <unit> typ_decls
%type <unit> typ_binding
%type <Ast.stmt Ast.decl> decl
%type <Ast.stmt> statement
%type <Ast.expr> expr
%type <Ast.expr> lvalue

%%

program:
| typ_decls p = program {p}
| g = global p = program {{ p with globals = p.Ast.globals @ g }}
| d = decl p = program {{ p with decls = p.Ast.decls @ [d] }}
| BEGIN main = list(terminated(statement, SEMI)) END p = program {{ p with main = Ast.Group main }}
| EOF {{ Ast.globals = []; decls = []; main = Ast.Group [] }}

typ_decls:
| TYPE nonempty_list(terminated(typ_binding, SEMI)) {()}

typ_binding:
| id = IDENT EQUALS ty = typ {Ast.(SymbolTable.add alias_table id ty)}

global:
| VAR r = nonempty_list(terminated(binding, SEMI))
  {List.concat_map (List.map (fun (id, typ) -> { Ast.id; typ; value = Ast.External })) r}

binding:
| r = separated_pair(separated_nonempty_list(COMMA, IDENT), COLON, typ)
  {let ids, typ = r in List.map (fun id -> (id, typ)) ids}

array_range:
| min_bound = INT DOTDOT max_bound = INT {(min_bound, max_bound)}

typ:
| LPAREN params = separated_list(COMMA, typ) RPAREN COLON ret = typ {Ast.TFunction (params, Some ret)}
| ARRAY LBRACK bounds = separated_nonempty_list(COMMA, array_range) RBRACK OF t = typ
  {
  let rec go = function
    | [(min_bound, max_bound)] -> Ast.TArray (t, min_bound, max_bound)
    | (min_bound, max_bound) :: rest -> Ast.TArray (go rest, min_bound, max_bound)
    | [] -> failwith "Nonempty list expected"
  in
  go bounds
  }
| RECORD fields = list(terminated(separated_pair(IDENT, COLON, typ), SEMI)) END {Ast.TRecord fields}
| INT64 {Ast.TInteger64}
| INT32 {Ast.TInteger32}
| INT16 {Ast.TInteger16}
| BOOLEAN {Ast.TBoolean}
| SINGLE {Ast.TSingle}
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
| VAR r = separated_pair(IDENT, COLON, typ) rv = option(ASSIGN rv = rvalue {rv})
  {
  let id, typ = r in
  match rv, typ with
  | Some (`Alloca i), Ast.TPointer typ -> Ast.Alloca (id, typ, i)
  | Some (`Alloca _), typ -> failwith @@ Format.asprintf "Non-pointer type for alloca: %a" Ast.pp_typ typ
  | Some (`Exp e), _ -> Ast.Group [Ast.Declare (id, typ); Ast.Assign (Var id, e)]
  | None, _ -> Ast.Declare (id, typ)
  }
| IF e = expr THEN thn = statement {Ast.If (e, thn, Group [])}
| IF e = expr THEN thn = statement ELSE els = statement {Ast.If (e, thn, els)}
| WHILE e = expr DO body = statement {Ast.While (e, body)}
| e1 = lvalue ASSIGN e2 = expr {Ast.Assign (e1, e2)}
| f = IDENT LPAREN exprs = separated_list(COMMA, expr) RPAREN {Ast.Call (f, exprs)}

lvalue:
| id = IDENT {Ast.Var id}
| e1 = lvalue LBRACK l = separated_nonempty_list(COMMA, expr) RBRACK
  {
  let rec go e = function
    | idx :: rest -> go (Ast.ArrayIndex (e, idx)) rest
    | [] -> e
  in
  go e1 l
  }
| e1 = lvalue DOT field = IDENT {Ast.RecordField (e1, field)}
| e = lvalue EXPONENT {Ast.Deref e}

rvalue:
| ALLOCA i = INT {`Alloca i}
| e = expr {`Exp e}

expr:
| LPAREN e = expr RPAREN {e}
| ATSIGN e = expr {Ast.Addrof e}
| e = expr EXPONENT {Ast.Deref e}
| LBRACK init = expr SEMI size = INT RBRACK {Ast.Array (init, size)}
| lhs = expr LBRACK l = separated_nonempty_list(COMMA, expr) RBRACK
  {
  let rec go e = function
    | idx :: rest -> go (Ast.ArrayIndex (e, idx)) rest
    | [] -> e
  in
  go lhs l
  }
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