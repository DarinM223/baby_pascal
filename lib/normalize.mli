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
    | Label of label * operands
  and operands = operand list

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

  (* destination goes before sources for operands *)
  type instr =
    | Assign of operand * operand
    | Call of operand * operand * operands
    | Goto of label * operands
    | Cbranch of operand * operand * cond * label * operands * label * operands
    | Return of operands
    | Uop of operand * Ast.uop * operand
    | Bop of operand * Ast.bop * operand * operand

  include
    Graph.Target
      with type label := label
       and type reg := reg
       and type cond := cond
       and type instr := instr
       and type operand := operand
       and type operands := operands

  val tombstone : operand
  val is_tombstone : operand -> bool
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
