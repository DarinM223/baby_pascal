module Name : sig
  type t

  val pp : Format.formatter -> t -> unit
end
module NameSet : Set.S with type elt = Name.t
module Target : sig
  include Graph.Target with type label = int * string
  type operand =
    | Const of int
    | Reg of reg
    | Label of label * reg list

  val name : string -> reg
  val reg : string -> operand
  val assign : dest:operand -> src:operand -> instr
  val call : reg -> operand list -> instr
  val uop : Ast.uop -> dest:operand -> src:operand -> instr
  val bop : Ast.bop -> dest:operand -> src1:operand -> src2:operand -> instr
end
module Cfg :
  Graph.S
    with type Target.label = Target.label
     and type Target.instr = Target.instr
     and type Target.reg = Target.reg
module Flow : Dataflow.S with module G = Cfg

val normalize : Ast.stmt list -> Cfg.graph
