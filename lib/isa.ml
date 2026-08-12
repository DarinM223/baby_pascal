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
  val is_pcopy : instr -> bool

  val clobber_regs : instr -> RegSet.t
  (** Get the set of registers that are clobbered when the instruction
      constrained by the pcopy finishes. *)

  val with_clobber_regs : RegSet.t -> instr -> instr
  (** Return the instruction with the given registers marked as registers that
      clobber the constrained instruction *)

  val modify_uses :
    (uses:operands -> num_hidden:int -> operands * int) -> instr -> instr
  val modify_defs :
    (defs:operands -> num_hidden:int -> operands * int) -> instr -> instr

  val num_hidden_uses : instr -> int
  (** Number of hidden uses starting from index 0. All uses after this number
      will be shown in the final assembly. *)

  val num_hidden_defs : instr -> int
  (** Number of hidden definitions starting from index 0. All definitions after
      will be shown in the final assembly. *)

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
    vreg_block : int Utils.IntHashtbl.t;
    new_stack_slot : int -> Target.operand;
    mutable curr_block : int;
    mutable stack_offset : int;
    mutable frame_pointer : Target.reg option;
  }
  val init : unit -> t
  val assign_vreg : t -> Target.reg_class -> 'a Undag.Target.t -> Target.reg
end
