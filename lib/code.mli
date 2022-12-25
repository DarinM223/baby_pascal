type op =
  | Neg
  | Not
  | Add
  | Sub
  | Mul
  | Div
  | And
  | Or
  | Goto
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne
  | Param
  | Call
  | Assign
  | Return
  | Nop

val pp_op : Format.formatter -> op -> unit
val show_op : op -> string

type addr = Const of int | Name of int | Temp of int | Empty

val pp_addr : Format.formatter -> addr -> unit
val show_addr : addr -> string

type quad = op * addr * addr * addr

val pp_quad : Format.formatter -> quad -> unit
val show_quad : quad -> string

type 'a node = {
  mutable value : 'a;
  pred : 'a node CCVector.vector;
  next : 'a node CCVector.vector;
}

type block = quad array

val counter : int ref
val fresh : unit -> int
val sym_table : (string, int) Hashtbl.t
val get_sym : string -> int
val op_of_uop : Ast.uop -> op
val op_of_bop : Ast.bop -> op
val normalize : Ast.stmt list -> quad CCVector.vector
val identifying_leaders : quad CCVector.vector -> block node

type set = bytes

type gen_kill_info = {
  gen : set array;
  kill : set array;
  gen_block : set;
  kill_block : set;
}

val gen_kill : block -> gen_kill_info