module type Target = sig
  type label
  type reg
  type regs = reg list
  type operand
  type operands = operand list
  type instr

  type cond = Instruction.Cond.t

  val goto : label -> operands -> instr
  val cbranch :
    args:operands -> cond -> label -> operands -> label -> operands -> instr
  val return : uses:operands -> instr

  val pp_reg : Format.formatter -> reg -> unit
  val equal_reg : reg -> reg -> bool
  val pp_instr : Format.formatter -> instr -> unit
  val equal_instr : instr -> instr -> bool
  val pp_regs : Format.formatter -> regs -> unit
  val show_regs : regs -> string
  val equal_regs : regs -> regs -> bool
  val pp_operand : Format.formatter -> operand -> unit
  val show_operand : operand -> string
  val equal_operand : operand -> operand -> bool
  val pp_operands : Format.formatter -> operands -> unit
  val show_operands : operands -> string
  val equal_operands : operands -> operands -> bool
end

module type Extra = sig
  type label
  type position
  type graph
  type uid
  val pp_label : Format.formatter -> label -> unit
  val equal_label : label -> label -> bool
  val position_of_int : int -> position
  val int_of_position : position -> int
  val pp_position : Format.formatter -> position -> unit
  val equal_position : position -> position -> bool
  val size : int
  val label_of_position : position -> label option
  val position_of_label : label option -> position
  val position_of_uid : uid -> position
  val successors : position -> position list
  val predecessors : position -> position list
  val graph : graph
end

module type S = sig
  module Target : Target
  type uid = int
  val pp_uid : Format.formatter -> uid -> unit
  val show_uid : uid -> string
  val equal_uid : uid -> uid -> bool
  val entry_uid : uid

  type label = uid * string
  val pp_label : Format.formatter -> label -> unit
  val show_label : label -> string
  val equal_label : label -> label -> bool

  type regs = Target.reg list
  val pp_regs : Format.formatter -> regs -> unit
  val show_regs : regs -> string
  val equal_regs : regs -> regs -> bool

  type info = {
    local : bool;
    args : regs;
  }
  val pp_info : Format.formatter -> info -> unit
  val show_info : info -> string
  val equal_info : info -> info -> bool

  type first =
    | Entry
    | Label of label * info
  val pp_first : Format.formatter -> first -> unit
  val show_first : first -> string
  val equal_first : first -> first -> bool

  type middle = Instruction of Target.instr
  val pp_middle : Format.formatter -> middle -> unit
  val show_middle : middle -> string
  val equal_middle : middle -> middle -> bool

  type last =
    | Exit
    | Branch of Target.instr * label
    | CBranch of Target.instr * label * label
    | Return of Target.instr
  val pp_last : Format.formatter -> last -> unit
  val show_last : last -> string
  val equal_last : last -> last -> bool

  type head =
    | First of first
    | Head of head * middle
  val pp_head : Format.formatter -> head -> unit
  val show_head : head -> string
  val equal_head : head -> head -> bool

  type tail =
    | Last of last
    | Tail of middle * tail
  val pp_tail : Format.formatter -> tail -> unit
  val show_tail : tail -> string
  val equal_tail : tail -> tail -> bool

  type zblock = head * tail
  val pp_zblock : Format.formatter -> zblock -> unit
  val show_zblock : zblock -> string
  val equal_zblock : zblock -> zblock -> bool

  type block = first * tail
  val pp_block : Format.formatter -> block -> unit
  val show_block : block -> string
  val equal_block : block -> block -> bool

  type graph
  val pp_graph : Format.formatter -> graph -> unit
  val show_graph : graph -> string
  val equal_graph : graph -> graph -> bool

  type zgraph = zblock * graph
  val pp_zgraph : Format.formatter -> zgraph -> unit
  val show_zgraph : zgraph -> string
  val equal_zgraph : zgraph -> zgraph -> bool

  type nodes = zgraph -> zgraph

  module Blocks : sig
    val iter : (uid -> block -> unit) -> graph -> unit
    val filter : (uid -> block -> bool) -> graph -> graph
    val fold : (uid -> block -> 'a -> 'a) -> graph -> 'a -> 'a
    val insert : block -> graph -> graph
    val union : graph -> graph -> graph
  end

  val exit_uid : graph -> uid
  val idd : label option -> uid
  val id : block -> uid
  val block_label : block -> label option
  val empty : graph
  val zip : zblock -> block
  val unzip : block -> zblock
  val firstt : head -> first
  val first : zblock -> first
  val lastt : tail -> last
  val last : zblock -> last
  val goto_start : zblock -> first * tail
  val goto_end : zblock -> head * last
  val map_first : (first -> first) -> zblock -> zblock
  val map_last : (last -> last) -> zblock -> zblock

  val focus_entry : graph -> zgraph
  val focus_exit : graph -> zgraph
  val focus : uid -> graph -> zgraph
  val unfocus : zgraph -> graph

  val splice_head : ?entry:uid -> head -> graph -> graph * head
  val splice_tail : ?entry:uid -> graph -> tail -> tail * graph
  val splice_head_only : head -> graph -> graph
  val remove_entry : graph -> tail * graph
  val splice_focus_entry : zgraph -> graph -> zgraph
  val splice_focus_exit : zgraph -> graph -> zgraph
  val expand : (middle -> graph) -> (last -> graph) -> graph -> graph

  val successors : last -> label list
  val reverse_postorder_dfs_from : uid -> graph -> block list
  val reverse_postorder_dfs : graph -> block list

  val unreachable : tail -> unit
  val instruction : Target.instr -> nodes
  val label : ?args:regs -> Target.label -> nodes
  val branch : ?args:Target.operands -> Target.label -> nodes
  val cbranch :
    ?ifso_args:Target.operands ->
    ?ifnot_args:Target.operands ->
    args:Target.operand list ->
    Target.cond ->
    ifso:Target.label ->
    ifnot:Target.label ->
    nodes
  val return : uses:Target.operands -> nodes
  val exit : nodes

  val precalculate_edges :
    graph ->
    (module Extra
       with type label = Target.label
        and type graph = graph
        and type position = int
        and type uid = uid)
end

module type Maker = functor (Target : Target with type label = int * string) ->
  S with module Target = Target

(* Interface of graph.ml *)
module type Intf = sig
  module type Target = Target
  module type S = S
  module type Extra = Extra
  module Make : Maker
end
