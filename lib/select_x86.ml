module Target = struct
  type label = Normalize.Target.label [@@deriving show, eq]
  type reg_class =
    | Int
    | Float
  [@@deriving show, eq]
  type physical_reg = int * reg_class [@@deriving show, eq]
  type reg_constr =
    | Any
    | OnReg
    | OnStack
    | UsePhysical of physical_reg
    | ReuseOperand of int
  [@@deriving show, eq]
  type reg =
    | Physical of physical_reg
    | Virtual of int * reg_class * reg_constr
  [@@deriving show, eq]
  type regs = reg list [@@deriving show, eq]
  type operand =
    | Imm of int
    | Reg of reg
    | MemAddr of {
        base : reg;
        index : reg;
        scale : int;
        displacement : int;
      }
    | StackSlot of int
    | Block of label
  [@@deriving show, eq]
  type operands = operand list [@@deriving show, eq]
  type instr = {
    instr : string;
    operands : operands;
  }
  [@@deriving show, eq]
  type cond = Instruction.Cond.t
  let goto l ops = { instr = "j"; operands = Block l :: ops }
  let cbranch ~args cond l1 l1args l2 l2args =
    {
      instr = Format.asprintf "cmp %a" Instruction.Cond.pp cond;
      operands = args @ [ Block l1 ] @ l1args @ [ Block l2 ] @ l2args;
    }
  let return ~uses = { instr = "ret"; operands = uses }
end

module NameHashtbl = Hashtbl.Make (struct
  include Normalize.Name
  let equal = equal
  let hash = Hashtbl.hash
end)
module Cfg = Graph.Make (Target)

let hashtbl_size = 100

let rec concat (t1 : Cfg.tail) (t2 : Cfg.tail) : Cfg.tail =
  match (t1 : Cfg.tail) with
  | Cfg.Last _ -> t2
  | Cfg.Tail (m, t) -> Cfg.Tail (m, concat t t2)

let select (_fresh_vreg : Target.reg_class -> Target.reg)
    (_mapping : Target.reg NameHashtbl.t) (_instr : Undag.Target.instr) :
    Cfg.tail =
  failwith ""

let codegen_block ((first, tail) : Undag.Cfg.block) : Cfg.block =
  let fresh_vreg =
    let c = ref (-1) in
    fun clz ->
      incr c;
      Target.(Virtual (!c, clz, Any))
  in
  let mapping = NameHashtbl.create hashtbl_size in
  let first =
    match first with
    | Undag.Cfg.Entry -> Cfg.Entry
    | Undag.Cfg.Label (l, i) ->
      let map_vreg n =
        let vreg = fresh_vreg Target.Int in
        NameHashtbl.add mapping n vreg;
        vreg
      in
      Cfg.Label (l, { local = i.local; args = List.map map_vreg i.args })
  in
  let rec go_tail (tail : Undag.Cfg.tail) : Cfg.tail =
    match tail with
    | Undag.Cfg.Last last -> begin
      match last with
      | Undag.Cfg.Exit -> Cfg.Last Cfg.Exit
      | Undag.Cfg.Branch (i, _) -> select fresh_vreg mapping i
      | Undag.Cfg.CBranch (i, _, _) -> select fresh_vreg mapping i
      | Undag.Cfg.Return i -> select fresh_vreg mapping i
    end
    | Undag.Cfg.Tail (Instruction i, rest) ->
      let tail = select fresh_vreg mapping i in
      concat tail (go_tail rest)
  in
  let tail = go_tail tail in
  (first, tail)
