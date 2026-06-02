open Lexing

let print_position fmt lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf fmt "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_buf lexbuf =
  try Some (Parser.program Lexer.token lexbuf)
  with Parser.Error ->
    Format.fprintf Format.err_formatter "%a: syntax error\n" print_position
      lexbuf;
    None

let parse_file filename =
  let inx = In_channel.open_text filename in
  let lexbuf = Lexing.from_channel inx in
  let program = parse_buf lexbuf in
  In_channel.close inx;
  program

let parse_string str =
  let lexbuf = Lexing.from_string str in
  parse_buf lexbuf
