{
  open Parser
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
| white { token lexbuf }
| newline { Lexing.new_line lexbuf; token lexbuf }
| '"' { read_string (Buffer.create 16) lexbuf }
| "//" { comment lexbuf }
| ':' {COLON}
| '.' {DOT}
| ',' {COMMA}
| '(' {LPAREN}
| ')' {RPAREN}
| '[' {LBRACK}
| ']' {RBRACK}
| '{' {LBRACE}
| '}' {RBRACE}
| '&' {AMPER}
| ":=" {ASSIGN}
| '=' {EQUALS}
| "<>" {NEQUALS}
| '<' {LT}
| "<=" {LE}
| '>' {GT}
| ">=" {GE}
| ';' {SEMI}
| '+' {PLUS}
| '-' {MINUS}
| '*' {TIMES}
| '/' {DIV}
| "alloca" {ALLOCA}
| "var" {VAR}
| "integer" {INTEGER}
| "boolean" {BOOLEAN}
| "double" {DOUBLE}
| "char" {CHAR}
| "true" {TRUE}
| "false" {FALSE}
| "void" {VOID}
| "function" {FUNCTION}
| "procedure" {PROCEDURE}
| "begin" {BEGIN}
| "end" {END}
| "if" {IF}
| "then" {THEN}
| "else" {ELSE}
| "do" {DO}
| "while" {WHILE}
| "not" {NOT}
| "and" {AND}
| "or" {OR}
| ['0'-'9']+ as i { INT (int_of_string i) }
| ['0'-'9']+ ("." ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)? as f {FLOAT (float_of_string f)}
| id as i {IDENT i}
| _ as c { print_char c; token lexbuf }
| eof { EOF }
and comment = parse
| newline { Lexing.new_line lexbuf; token lexbuf }
| _ { comment lexbuf }
and read_string buf = parse
  | '"'                         { STRING (Buffer.contents buf) }
  | '\\' '"'                    { Buffer.add_char buf '"'; read_string buf lexbuf }
  | '\\' '\\'                   { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'n'                    { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 't'                    { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\' '\n']+ as text  { Buffer.add_string buf text; read_string buf lexbuf }
  | '\n'                        { failwith "newline in string" }
  | eof                         { failwith "unterminated string" }
  | _                           { failwith "invalid escape sequence" }