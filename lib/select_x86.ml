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

module Cfg = Graph.Make (Target)

let codegen_block (_block : Undag.Cfg.block) : Cfg.block = failwith ""
