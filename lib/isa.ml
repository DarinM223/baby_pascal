module type Target = sig
  type reg_class [@@deriving show, eq]
  type physical_reg [@@deriving show, eq]
  type reg_constr =
    | Any
    | OnReg
    | OnStack
    | UsePhysical of physical_reg
    | ReuseOperand of virtual_reg
  and virtual_reg = {
    id : int;
    reg_class : reg_class;
    mutable reg : reg;
    mutable reg_constr : reg_constr;
  }
  and reg =
    | Physical of physical_reg
    | Virtual of virtual_reg
    | Tombstone
  [@@deriving show]
  include Instruction.Target with type reg := reg
  val index : reg -> int
  val reg : reg -> operand
  val destruct_reg : operand -> reg option

  val fold_reg_operand :
    ('a -> reg -> 'a * reg) -> 'a -> operand -> 'a * operand
  val subst_reg_operand : (reg -> reg) -> operand -> operand
  val to_colored : operand -> operand

  module Reg : sig
    type t = reg
    val is_tombstone : reg -> bool
    val tombstone : reg
    val of_operand : operand -> reg option
    val to_operand : reg -> operand
    val equal : reg -> reg -> bool
    val compare : reg -> reg -> int
    val hash : reg -> int
    val reg : reg -> reg
  end
  module RegSet : Set.S with type elt = reg
  module RegMap : Map.S with type key = reg

  type pcopy = (operand * operand) list [@@deriving show, eq]

  val map_reg_uses : (reg -> reg) -> instr -> instr
  val fold_reg_uses : ('a -> reg -> 'a * reg) -> 'a -> instr -> 'a * instr
  val fold_reg_defs : ('a -> reg -> 'a * reg) -> 'a -> instr -> 'a * instr
  val uses : instr -> RegSet.t
  val defs : instr -> RegSet.t

  val constrained : physical_reg -> reg -> reg
  val reuse : reg -> reg -> reg
  val reuse_op : operand -> operand -> operand
  val cond_mapping : (Graph.Cond.t * string) list
  val instr : string -> defs:operands -> uses:operands -> instr
  val mov : dest:operand -> src:operand -> instr
  val pcopy : dests:operands -> srcs:operands -> instr
end

module type State = sig
  module Target : Target
  type t = {
    fresh_vreg : Target.reg_class -> Target.reg;
    mapping : Target.operand Normalize.NameHashtbl.t;
    curr_block : int ref;
    vreg_block : int Utils.IntHashtbl.t;
    stack_offset : int ref;
    new_stack_slot : int -> Target.operand;
  }
  val init : unit -> t
  val assign_vreg : t -> Target.reg_class -> 'a Undag.Target.t -> Target.reg
end
