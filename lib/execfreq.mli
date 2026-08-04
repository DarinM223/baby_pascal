(** Block execution frequency from the paper "Static Branch Frequency and
    Program Profile Analysis" *)

module type Requirements = sig
  module Target : Graph_intf.Target
  val instr_name : Target.instr -> string
  val imm : Target.operand -> int option
  val uses : Target.instr -> Target.operands
  val call : string
  val ret : string
  val cond_mapping : (Graph_intf.Cond.t * string) list
  val exit : string
end

module Make : functor
  (G : Graph.S
         with type label = int * string
          and type Target.label = int * string)
  (Loop : Loopnesting.S
            with type Dom.label = G.label
             and type Dom.graph = G.graph
             and type Dom.position = int
             and type Dom.uid = G.uid)
  (_ : Requirements with module Target = G.Target)
  -> sig
  val pp_prob : Format.formatter -> float array array -> unit
  val pp_bfreq : Format.formatter -> float array -> unit
  val heuristics :
    (string
    * float
    * (Loop.Dom.position -> Loop.Dom.position -> Loop.Dom.position -> bool))
    list
  val prob : float array array
  val bfreq : float array
  val freq : float array array
  val inner_to_outer_loops : Loop.Dom.position array
  val calc_branch_prob : unit -> unit
  val compute_freq : unit -> unit
end
