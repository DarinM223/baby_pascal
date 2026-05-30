{
  open Parser
}

rule token = parse
| [' ' '\t'] { token lexbuf }
| ':' {COLON}
| '(' {LPAREN}
| ')' {RPAREN}
| ":=" {ASSIGN}
| '=' {EQUALS}
| ';' {SEMI}
| '+' {PLUS}
| '-' {MINUS}
| '*' {TIMES}
| "var" {VAR}
| "integer" {INTEGER}
| "boolean" {BOOLEAN}
| "void" {VOID}
| ['0'-'9']+ as i { INT (int_of_string i) }
| ['A'-'Z''a'-'z']+ as i {IDENT i}
| eof { EOF }