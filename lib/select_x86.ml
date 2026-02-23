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
    defs : operands;
    uses : operands;
  }
  [@@deriving show, eq]
  type cond = Instruction.Cond.t
  let goto l ops = { instr = "j"; defs = []; uses = Block l :: ops }
  let cbranch ~args cond l1 l1args l2 l2args =
    {
      instr = Format.asprintf "cmp %a" Instruction.Cond.pp cond;
      uses = args @ [ Block l1 ] @ l1args @ [ Block l2 ] @ l2args;
      defs = [];
    }
  let return ~uses = { instr = "ret"; uses; defs = [] }
end

module NameHashtbl = Hashtbl.Make (struct
  include Normalize.Name
  let equal = equal
  let hash = Hashtbl.hash
end)
module Cfg = Graph.Make (Target)

let ( let* ) = ( @@ )
let hashtbl_size = 100

let rec select (fresh_vreg : Target.reg_class -> Target.reg)
    (mapping : Target.reg NameHashtbl.t) (instr : Undag.Target.instr)
    (k : Target.operand -> Cfg.tail) : Cfg.tail =
  let assign_vreg clz = function
    | Undag.Target.Reg n ->
      let vreg = fresh_vreg clz in
      NameHashtbl.add mapping n vreg;
      vreg
    | _ -> failwith "assign_vreg: expected destination to be register"
  in
  match instr with
  | Undag.Target.Assign (dest, src) ->
    let dest = Target.Reg (assign_vreg Target.Int dest) in
    let* src =
      match src with
      | Undag.Target.Instr src -> select fresh_vreg mapping src
      | Undag.Target.Const i -> fun k -> k (Target.Imm i)
      | Undag.Target.Reg r ->
        fun k -> k (Target.Reg (NameHashtbl.find mapping r))
      | Undag.Target.Label (l, _) -> fun k -> k (Target.Block l)
    in
    let instr = { Target.instr = "mov"; defs = [ dest ]; uses = [ src ] } in
    Cfg.(Tail (Instruction instr, k dest))
  | Undag.Target.Call (_, _, _) -> failwith ""
  | Undag.Target.Return _ -> failwith ""
  | Undag.Target.Uop (_, _, _) -> failwith ""
  | Undag.Target.Bop (_, _, _, _) -> failwith ""
  | Undag.Target.Goto (_, _) -> failwith ""
  | Undag.Target.Cbranch (_, _, _, _, _, _, _) -> failwith ""

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
  let endd = Cfg.Last Cfg.Exit in
  let rec go_tail (tail : Undag.Cfg.tail) : Cfg.tail =
    match tail with
    | Undag.Cfg.Last last -> begin
      match last with
      | Undag.Cfg.Exit -> endd
      | Undag.Cfg.Branch (i, _) -> select fresh_vreg mapping i (Fun.const endd)
      | Undag.Cfg.CBranch (i, _, _) ->
        select fresh_vreg mapping i (Fun.const endd)
      | Undag.Cfg.Return i -> select fresh_vreg mapping i (Fun.const endd)
    end
    | Undag.Cfg.Tail (Instruction i, rest) ->
      select fresh_vreg mapping i (Fun.const (go_tail rest))
  in
  let tail = go_tail tail in
  (first, tail)
