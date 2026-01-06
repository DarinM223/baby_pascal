module Target : sig
  include Graph.Target with type label = int * string
  type operand =
    | Const of int
    | Reg of reg
    | Label of label

  val reg : string -> operand
  val assign : dest:operand -> src:operand -> instr
  val call : reg -> operand list -> instr
  val uop : Ast.uop -> dest:operand -> src:operand -> instr
  val bop : Ast.bop -> dest:operand -> src1:operand -> src2:operand -> instr
end
module Cfg : Graph.S with module Target := Target

val normalize : Ast.stmt list -> Cfg.graph
