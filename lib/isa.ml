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

module type Select = sig
  module Graph : Graph.S
  module State : State
  val select :
    State.t ->
    Undag.Target.instr ->
    (Graph.Target.operand -> Graph.tail) ->
    Graph.tail
  val reg_class_of_operand : Undag.Target.operand -> State.Target.reg_class
  val call_conv :
    caller:bool ->
    State.t ->
    State.Target.reg_class ->
    int ->
    Graph.Target.operand
end

module Codegen
    (Target : Target)
    (Cfg :
      Graph.S
        with type Target.reg = Target.reg
         and type Target.instr = Target.instr
         and type Target.operand = Target.operand
         and type Target.operands = Target.operands)
    (Select : Select with module Graph = Cfg and module State.Target = Target) =
struct
  let codegen_block (state : Select.State.t) ((first, tail) : Undag.Cfg.block) :
      Cfg.block =
    let first =
      match first with
      | Undag.Cfg.Entry -> Cfg.Entry
      | Undag.Cfg.Label (l, i) ->
        let map_vreg n =
          Select.(
            State.assign_vreg state (reg_class_of_operand (Reg n)) (Reg n))
        in
        Cfg.Label (l, { local = i.local; args = List.map map_vreg i.args })
    in
    let endd = Cfg.Last Cfg.Exit in
    let rec go_tail (tail : Undag.Cfg.tail) : Cfg.tail =
      match tail with
      | Undag.Cfg.Last last ->
        begin match last with
        | Undag.Cfg.Exit -> endd
        | Undag.Cfg.Branch (i, _) -> Select.select state i (Fun.const endd)
        | Undag.Cfg.CBranch (i, _, _) -> Select.select state i (Fun.const endd)
        | Undag.Cfg.Return i -> Select.select state i (Fun.const endd)
        end
      | Undag.Cfg.Tail (Instruction i, rest) ->
        Select.select state i (fun _ -> go_tail rest)
    in
    let tail = go_tail tail in
    (first, tail)

  let codegen_function ?(args = []) (state : Select.State.t)
      (graph : Undag.Cfg.graph) : Target.reg list * Cfg.graph =
    let srcs =
      List.mapi
        (fun i arg ->
          Select.call_conv ~caller:false state
            (Select.reg_class_of_operand (Reg arg))
            i)
        args
    in
    let reg_ops =
      List.filter_map (fun op ->
          match Target.destruct_reg op with
          | Some r -> Some r
          | _ -> None)
    in
    let dests =
      List.map
        (fun arg ->
          Target.reg
            Select.(
              State.assign_vreg state (reg_class_of_operand (Reg arg)) (Reg arg)))
        args
    in
    let pcopy = Cfg.Instruction (Target.pcopy ~dests ~srcs) in
    let blocks = Undag.Cfg.reverse_postorder_dfs graph in
    let graph =
      List.fold_left
        (fun acc block ->
          state.curr_block <- Undag.Cfg.id block;
          Cfg.Blocks.insert (codegen_block state block) acc)
        Cfg.empty blocks
    in
    let zblock, graph = Cfg.focus_entry graph in
    match zblock with
    | First Entry, tail when List.length args > 0 ->
      (reg_ops srcs, Cfg.unfocus ((First Entry, Tail (pcopy, tail)), graph))
    | _ -> (reg_ops srcs, Cfg.unfocus (zblock, graph))

  let codegen_test_helper ?(args = []) state cfg =
    let extra = Normalize.Cfg.precalculate_edges cfg in
    let module Extra = (val extra) in
    let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
    let a_orig = Construct.calc_a_orig cfg in
    let live = Construct.calc_live cfg in
    let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
    let cfg = Construct.rename_variables (module Dom) cfg in
    let cfg =
      Normalize.Cfg.Blocks.fold
        (fun _ block acc -> Undag.Cfg.Blocks.insert (Undag.undag block) acc)
        cfg Undag.Cfg.empty
    in
    codegen_function ~args:(List.map (fun arg -> (arg, 0)) args) state cfg
end
