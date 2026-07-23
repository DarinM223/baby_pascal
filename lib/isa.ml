module type Target = sig
  type label = Normalize.Target.label
  val pp_label : Format.formatter -> label -> unit
  val show_label : label -> string
  val equal_label : label -> label -> bool

  type reg_class [@@deriving show, eq]
  type physical_reg [@@deriving eq]
  type reg
  val pp_reg : Format.formatter -> reg -> unit
  val show_reg : reg -> string
  val index : reg -> int
  val equal_reg : reg -> reg -> bool

  type regs = reg list
  val pp_regs : Format.formatter -> regs -> unit
  val show_regs : regs -> string
  val equal_regs : regs -> regs -> bool

  type operand
  val equal_operand : operand -> operand -> bool
  val pp_operand' :
    (Format.formatter -> reg -> unit) -> Format.formatter -> operand -> unit
  val pp_operand : Format.formatter -> operand -> unit
  val show_operand : operand -> string

  val label : label -> operand list -> operand
  val destruct_label : operand -> (label * operand list) option

  val reg : reg -> operand

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
  val is_tombstone : operand -> bool
  type operands = operand list
  val pp_operands : Format.formatter -> operands -> unit
  val show_operands : operands -> string
  val equal_operands : operands -> operands -> bool

  type pcopy = (operand * operand) list
  val pp_pcopy : Format.formatter -> pcopy -> unit
  val show_pcopy : pcopy -> string
  val equal_pcopy : pcopy -> pcopy -> bool

  type instr
  val equal_instr : instr -> instr -> bool
  val pp_instr : Format.formatter -> instr -> unit
  val show_instr : instr -> string

  val srcs : instr -> operands
  val dests : instr -> operands
  val fold_uses : ('a -> operand -> 'a * operand) -> 'a -> instr -> 'a * instr
  val map_uses : (operand -> operand) -> instr -> instr
  val map_reg_uses : (reg -> reg) -> instr -> instr
  val fold_reg_uses : ('a -> reg -> 'a * reg) -> 'a -> instr -> 'a * instr
  val fold_defs : ('a -> operand -> 'a * operand) -> 'a -> instr -> 'a * instr
  val map_defs : (operand -> operand) -> instr -> instr
  val fold_reg_defs : ('a -> reg -> 'a * reg) -> 'a -> instr -> 'a * instr
  val regset_of_operand : operand -> RegSet.t
  val uses : instr -> RegSet.t
  val defs : instr -> RegSet.t

  type cond = Instruction.Cond.t
  val pp_cond : Format.formatter -> cond -> unit
  val show_cond : cond -> string
  val equal_cond : cond -> cond -> bool

  val constrained : physical_reg -> reg -> reg
  val reuse : reg -> reg -> reg
  val reuse_op : operand -> operand -> operand
  val goto : label -> operand list -> instr
  val cond_mapping : (Instruction.Cond.t * string) list
  val cbranch :
    args:operand list ->
    Instruction.Cond.t ->
    label ->
    operand list ->
    label ->
    operand list ->
    instr
  val return : uses:operands -> instr
  val instr : string -> defs:operands -> uses:operands -> instr
  val mov : dest:operand -> src:operand -> instr
  val pcopy : dests:operands -> srcs:operands -> instr
  val is_side_effectful : 'a -> bool
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
