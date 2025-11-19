module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

module type Target = sig
  type label
  type reg
  type instr

  type cond =
    | LT
    | LE
    | GT
    | GE
    | EQ
    | NE

  val goto : label -> instr
  val cbranch : uses:reg list -> cond -> label -> label -> instr
  val return : uses:reg list -> instr

  val pp_reg : Format.formatter -> reg -> unit
  val pp_instr : Format.formatter -> instr -> unit
end

module type S = sig
  module Target : Target
  type uid = int
  val pp_uid : Format.formatter -> uid -> unit
  val show_uid : uid -> string
  val entry_uid : int

  type label = uid * string
  val pp_label : Format.formatter -> label -> unit
  val show_label : label -> string

  type regs = Target.reg list
  val pp_regs : Format.formatter -> regs -> unit
  val show_regs : regs -> string

  type local = Local of bool
  val pp_local : Format.formatter -> local -> unit
  val show_local : local -> string

  type first =
    | Entry
    | Label of label * local
  val pp_first : Format.formatter -> first -> unit
  val show_first : first -> string

  type middle = Instruction of Target.instr
  val pp_middle : Format.formatter -> middle -> unit
  val show_middle : middle -> string

  type last =
    | Exit
    | Branch of Target.instr * label
    | CBranch of Target.instr * label * label
    | Return of Target.instr * regs
  val pp_last : Format.formatter -> last -> unit
  val show_last : last -> string

  type head =
    | First of first
    | Head of head * middle
  val pp_head : Format.formatter -> head -> unit
  val show_head : head -> string

  type tail =
    | Last of last
    | Tail of middle * tail
  val pp_tail : Format.formatter -> tail -> unit
  val show_tail : tail -> string

  type zblock = head * tail
  val pp_zblock : Format.formatter -> zblock -> unit
  val show_zblock : zblock -> string

  type block = first * tail
  val pp_block : Format.formatter -> block -> unit
  val show_block : block -> string

  type graph = block IntMap.t
  type zgraph = zblock * graph
  type nodes = zgraph -> zgraph

  module Blocks : sig
    val insert : block -> graph -> graph
    val union : graph -> graph -> graph
  end

  val id : block -> uid
  val empty : graph
  val zip : zblock -> block
  val unzip : block -> zblock
  val firstt : head -> first
  val first : zblock -> first
  val lastt : tail -> last
  val last : zblock -> last
  val goto_start : zblock -> first * tail
  val goto_end : zblock -> head * last

  val entry : graph -> zgraph
  val exit : graph -> zgraph
  val focus : uid -> graph -> zgraph
  val unfocus : zgraph -> graph

  val splice_head : head -> graph -> graph * head
  val splice_tail : graph -> tail -> tail * graph
  val splice_head_only : head -> graph -> graph
  val remove_entry : graph -> tail * graph
  val splice_focus_entry : zgraph -> graph -> zgraph
  val splice_focus_exit : zgraph -> graph -> zgraph
  val expand : (middle -> graph) -> (last -> graph) -> graph -> graph

  val successors : last -> label list
  val reverse_postorder_dfs : graph -> block list

  val unreachable : tail -> unit
  val instruction : Target.instr -> nodes
  val label : Target.label -> nodes
  val branch : Target.label -> nodes
  val cbranch :
    Target.reg list ->
    Target.cond ->
    ifso:Target.label ->
    ifnot:Target.label ->
    nodes
  val return : uses:regs -> nodes
end

module type Maker = functor (Target : Target with type label = int * string) ->
  S with module Target = Target

(* Interface of graph.ml *)
module type Intf = sig
  module type Target = Target
  module type S = S
  module Make : Maker
end
