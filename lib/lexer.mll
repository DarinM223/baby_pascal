{
  open Parser
}

rule token = parse
| [' ' '\t'] { token lexbuf }
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
| "var" {VAR}
| "integer" {INTEGER}
| "boolean" {BOOLEAN}
| "true" {TRUE}
| "false" {FALSE}
| "void" {VOID}
| "function" {FUNCTION}
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
| ['A'-'Z''a'-'z']+ as i {IDENT i}
| eof { EOF }