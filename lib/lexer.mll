{
  open Parser

  let code_char base digits =
    let prefix = if base = 8 then "0o" else "0x" in
    let n = int_of_string (prefix ^ digits) in
    if n > 255 then failwith "character code out of range";
    Char.chr n
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let oct = ['0'-'7']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']

rule token = parse
| white { token lexbuf }
| newline { Lexing.new_line lexbuf; token lexbuf }
| '"' { read_string (Buffer.create 16) lexbuf }
| '\'' { read_char lexbuf }
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
| "0x" hex+ as i { INT (int_of_string i) }
| "0X" hex+ as i { INT (int_of_string i) }
| ['0'-'9']+ as i { INT (int_of_string i) }
| ['0'-'9']+ ("." ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)? as f {FLOAT (float_of_string f)}
| id as i {IDENT i}
| _ as c { print_char c; token lexbuf }
| eof { EOF }
and comment = parse
| newline { Lexing.new_line lexbuf; token lexbuf }
| _ { comment lexbuf }
and read_string buf = parse
  | '"'                          { STRING (Buffer.contents buf) }
  | '\\' '"'                     { Buffer.add_char buf '"'; read_string buf lexbuf }
  | '\\' '\\'                    { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'n'                     { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 't'                     { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | '\\' 'x' (hex hex as digits) { Buffer.add_char buf (code_char 16 digits); read_string buf lexbuf }
  | '\\' (oct oct oct as digits) { Buffer.add_char buf (code_char 8 digits); read_string buf lexbuf }
  | [^ '"' '\\' '\n']+ as text   { Buffer.add_string buf text; read_string buf lexbuf }
  | '\n'                         { failwith "newline in string" }
  | eof                          { failwith "unterminated string" }
  | _                            { failwith "invalid escape sequence" }
and read_char = parse
  | '\\' '\''                    { finish_char '\'' lexbuf }
  | '\\' '\\'                    { finish_char '\\' lexbuf }
  | '\\' 'n'                     { finish_char '\n' lexbuf }
  | '\\' 't'                     { finish_char '\t' lexbuf }
  | '\\' 'x' (hex hex as digits) { finish_char (code_char 16 digits) lexbuf }
  | '\\' (oct oct oct as digits) { finish_char (code_char 8 digits) lexbuf }
  | '\n'                         { failwith "newline in character literal" }
  | eof                          { failwith "unterminated character literal" }
  | _ as c                       { finish_char c lexbuf }
and finish_char c = parse
  | '\'' { CHAR_LIT c }
  | _    { failwith "character literal can only contain one character" }