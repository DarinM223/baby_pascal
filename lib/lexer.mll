{
  open Parser
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule token = parse
| white { token lexbuf }
| newline { Lexing.new_line lexbuf; token lexbuf }
| "//" { comment lexbuf }
| ':' {COLON}
| ',' {COMMA}
| '(' {LPAREN}
| ')' {RPAREN}
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
| "var" {VAR}
| "integer" {INTEGER}
| "boolean" {BOOLEAN}
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
| id as i {IDENT i}
| _ as c { print_char c; token lexbuf }
| eof { EOF }
and comment = parse
| newline { Lexing.new_line lexbuf; token lexbuf }
| _ { comment lexbuf }