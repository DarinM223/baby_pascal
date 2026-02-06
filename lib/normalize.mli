module Name : sig
  type t
  val pp : Format.formatter -> t -> unit
  val equal : t -> t -> bool
  val tombstone : t
  val is_tombstone : t -> bool
  val label : t -> string
  val index : t -> int
  val update_index : int -> t -> t
end
module NameSet : sig
  include Set.S with type elt = Name.t
  val pp : Format.formatter -> t -> unit
end
module Target : sig
  type label = int * string
  type reg = Name.t
  type operand =
    | Const of int
    | Reg of reg
    | Label of label * reg list
  include
    Graph.Target
      with type label := label
       and type reg := reg
       and type operand := operand

  val srcs : instr -> operand list
  val dests : instr -> operand list
  val uses : instr -> NameSet.t
  val defs : instr -> NameSet.t
  val map_uses : (operand -> operand) -> instr -> instr
  val map_defs : (operand -> operand) -> instr -> instr
  val name : string -> reg
  val reg : string -> operand
  val assign : dest:operand -> src:operand -> instr
  val call : dest:operand -> operand -> operand list -> instr
  val uop : Ast.uop -> dest:operand -> src:operand -> instr
  val bop : Ast.bop -> dest:operand -> src1:operand -> src2:operand -> instr
end
module Cfg :
  Graph.S
    with type Target.label = Target.label
     and type Target.instr = Target.instr
     and type Target.reg = Target.reg
     and type Target.operand = Target.operand
module Flow : Dataflow.S with module G = Cfg

val normalize : Ast.stmt list -> Cfg.graph
