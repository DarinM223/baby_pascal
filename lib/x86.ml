module Target = struct
  type label = Normalize.Target.label [@@deriving show, eq]
  type reg_class =
    | Int
    | Float
  [@@deriving eq]
  type physical_reg = int * reg_class * string [@@deriving eq]
  type reg_constr =
    | Any
    | OnReg
    | OnStack
    | UsePhysical of physical_reg
    | ReuseOperand of reg
  and virtual_reg = {
    id : int;
    reg_class : reg_class;
    mutable reg_constr : reg_constr;
  }
  and reg =
    | Physical of physical_reg
    | Virtual of virtual_reg
  [@@deriving eq]
  let pp_reg_class fmt = function
    | Int -> Format.fprintf fmt ""
    | Float -> Format.fprintf fmt "f"
  let show_reg_class = Format.asprintf "%a" pp_reg_class
  let rec pp_reg_constr fmt = function
    | Any -> Format.fprintf fmt "any"
    | OnReg -> Format.fprintf fmt "reg"
    | OnStack -> Format.fprintf fmt "stack"
    | UsePhysical r -> Format.fprintf fmt "(%%%a)" pp_reg (Physical r)
    | ReuseOperand r ->
      let id =
        match r with
        | Physical (id, _, _) -> id
        | Virtual v -> v.id
      in
      Format.fprintf fmt "(reuse=%%%d)" id

  and pp_reg fmt = function
    | Physical (_, _, s) -> Format.fprintf fmt "%s" s
    | Virtual v ->
      Format.fprintf fmt "%d%a%a" v.id pp_reg_class v.reg_class pp_reg_constr
        v.reg_constr
  let show_reg_constr = Format.asprintf "%a" pp_reg_constr
  let show_reg = Format.asprintf "%a" pp_reg

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
    | Label of label
  [@@deriving eq]
  let pp_operand fmt = function
    | Imm i -> Format.fprintf fmt "$%d" i
    | Reg r -> Format.fprintf fmt "%%%a" pp_reg r
    | MemAddr addr ->
      Format.fprintf fmt "%d(%%%a,%%%a,%d)" addr.displacement pp_reg addr.base
        pp_reg addr.index addr.scale
    | StackSlot offset -> Format.fprintf fmt "%d(%%rsp)" offset
    | Label l -> Format.fprintf fmt "%s" (snd l)
  let show_operand = Format.asprintf "%a" pp_operand

  type operands = operand list [@@deriving show, eq]
  type pcopy = (operand * operand) list [@@deriving show, eq]
  type instr = {
    instr : string;
    defs : operands;
    uses : operands;
  }
  [@@deriving eq]
  let pp_instr fmt i =
    match i.instr with
    | "pcopy" ->
      Format.fprintf fmt "pcopy %a" pp_pcopy (List.combine i.defs i.uses)
    | _ ->
      let pp_sep fmt () = Format.fprintf fmt ", " in
      let pp_operands = Format.pp_print_list ~pp_sep pp_operand in
      Format.fprintf fmt "%s %a" i.instr pp_operands (i.defs @ i.uses)
  let show_instr = Format.asprintf "%a" pp_instr

  type cond = Instruction.Cond.t
  let index = function
    | Physical (id, _, _) -> id
    | Virtual v -> v.id
  let constrained physical_reg = function
    | Physical p ->
      if p <> physical_reg then
        failwith "constrained: physical registers conflict"
      else Physical p
    | Virtual v ->
      v.reg_constr <- UsePhysical physical_reg;
      Virtual v
  let reuse reg = function
    | Physical _ -> failwith "reuse: expected virtual register"
    | Virtual v ->
      v.reg_constr <- ReuseOperand reg;
      Virtual v
  let reuse_op op dest =
    match (op, dest) with
    | Reg reg, Reg dest -> Reg (reuse reg dest)
    | _ -> failwith "reuse_op: expected register"
  let goto l ops = { instr = "j"; defs = []; uses = Label l :: ops }
  let cbranch ~args cond l1 l1args l2 l2args =
    {
      instr = Format.asprintf "cmp %a" Instruction.Cond.pp cond;
      uses = args @ [ Label l1 ] @ l1args @ [ Label l2 ] @ l2args;
      defs = [];
    }
  let return ~uses = { instr = "ret"; uses; defs = [] }
  let instr instr ~defs ~uses = { instr; defs; uses }
  let mov ~dest ~src = instr "movq" ~defs:[ dest ] ~uses:[ src ]
  let pcopy ~dests ~srcs = instr "pcopy" ~defs:dests ~uses:srcs
end

module Regs = struct
  (* todo: handle overlapping subregisters *)
  let rax = (0, Target.Int, "rax")
  let rbx = (1, Target.Int, "rbx")
  let rcx = (2, Target.Int, "rcx")
  let rdx = (3, Target.Int, "rdx")
  let rsi = (4, Target.Int, "rsi")
  let rdi = (5, Target.Int, "rdi")
  let rsp = (6, Target.Int, "rsp")
  let rbp = (7, Target.Int, "rbp")
  let r8 = (8, Target.Int, "r8")
  let r9 = (9, Target.Int, "r9")
  let r10 = (10, Target.Int, "r10")
  let r11 = (11, Target.Int, "r11")
  let r12 = (12, Target.Int, "r12")
  let r13 = (13, Target.Int, "r13")
  let r14 = (14, Target.Int, "r14")
  let r15 = (15, Target.Int, "r15")

  let caller_save = [ rax; rcx; rdx; rsi; rdi; r8; r9; r10; r11 ]
end

module Cfg = Graph.Make (Target)
module Flow = Dataflow.Make (Cfg)

module Printer = struct
  type label = Cfg.label
  let pp_label fmt (_, l) = Format.fprintf fmt "%s" l
  type first = Cfg.first =
    | Entry
    | Label of label * Cfg.info
  type middle = Cfg.middle = Instruction of Target.instr
  type last = Cfg.last =
    | Exit
    | Branch of Target.instr * label
    | CBranch of Target.instr * label * label
    | Return of Target.instr
  let pp_sep fmt () = Format.fprintf fmt ", "
  let pp_first fmt = function
    | Entry -> ()
    | Label (l, info) ->
      Format.fprintf fmt "%a(local=%b)(%a):" pp_label l info.local
        (Format.pp_print_list ~pp_sep Target.pp_reg)
        info.args
  let pp_middle fmt (Instruction instr) =
    Format.fprintf fmt "%a" Target.pp_instr instr
  let pp_last fmt = function
    | Exit -> Format.fprintf fmt "exit"
    | Branch (i, _) | CBranch (i, _, _) | Return i ->
      Format.fprintf fmt "%a" Target.pp_instr i

  type head = Cfg.head =
    | First of first
    | Head of head * middle
  let rec pp_head fmt = function
    | First f -> Format.fprintf fmt "%a@\n" pp_first f
    | Head (h, m) -> Format.fprintf fmt "%a  %a@\n" pp_head h pp_middle m
  type tail = Cfg.tail =
    | Last of last
    | Tail of middle * tail
  let rec pp_tail fmt = function
    | Last l -> Format.fprintf fmt "%a@\n" pp_last l
    | Tail (m, t) -> Format.fprintf fmt "%a@\n  %a" pp_middle m pp_tail t
  type block = first * tail
  let pp_block fmt (f, t) = Format.fprintf fmt "%a@\n  %a" pp_first f pp_tail t
  let pp_graph fmt =
    Cfg.Blocks.iter (fun _ block -> Format.fprintf fmt "%a" pp_block block)
end
