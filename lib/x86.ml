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
    mutable reg : reg;
    mutable reg_constr : reg_constr;
  }
  and reg =
    | Physical of physical_reg
    | Virtual of virtual_reg
    | Tombstone
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
        | Tombstone -> failwith "reusing tombstone"
      in
      Format.fprintf fmt "(reuse=%%%d)" id

  and pp_reg fmt = function
    | Physical (_, _, s) -> Format.fprintf fmt "%s" s
    | Virtual v ->
      begin match v.reg with
      | Physical _ as r -> Format.fprintf fmt "%a(%d)" pp_reg r v.id
      | _ ->
        Format.fprintf fmt "%d%a%a" v.id pp_reg_class v.reg_class pp_reg_constr
          v.reg_constr
      end
    | Tombstone -> ()
  let show_reg_constr = Format.asprintf "%a" pp_reg_constr
  let show_reg = Format.asprintf "%a" pp_reg
  let index = function
    | Physical (id, _, _) -> id
    | Virtual v -> v.id
    | Tombstone -> failwith "index: got tombstone"
  let equal_reg r1 r2 = Int.equal (index r1) (index r2)

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
    | Label of label * operand list
  [@@deriving eq]
  let pp_sep fmt () = Format.fprintf fmt ", "
  let rec pp_operand' pp_reg fmt = function
    | Imm i -> Format.fprintf fmt "$%d" i
    | Reg r -> Format.fprintf fmt "%%%a" pp_reg r
    | MemAddr addr ->
      Format.fprintf fmt "%d(%%%a,%%%a,%d)" addr.displacement pp_reg addr.base
        pp_reg addr.index addr.scale
    | StackSlot offset -> Format.fprintf fmt "%d(%%rsp)" offset
    | Label (l, []) -> Format.fprintf fmt "%s" (snd l)
    | Label (l, args) ->
      Format.fprintf fmt "%s(%a)" (snd l)
        (Format.pp_print_list ~pp_sep (pp_operand' pp_reg))
        args
  let pp_operand = pp_operand' pp_reg
  let show_operand = Format.asprintf "%a" (pp_operand' pp_reg)
  let label label args = Label (label, args)
  let destruct_label = function
    | Label (l, args) -> Some (l, args)
    | _ -> None
  let rec to_colored =
    let to_colored_reg = function
      | Virtual { reg; _ } -> reg
      | reg -> reg
    in
    function
    | Reg r -> Reg (to_colored_reg r)
    | MemAddr ({ base : reg; index : reg; _ } as addr) ->
      MemAddr
        { addr with base = to_colored_reg base; index = to_colored_reg index }
    | Label (l, ops) -> Label (l, List.map to_colored ops)
    | (Imm _ | StackSlot _) as op -> op
  module Reg = struct
    type t = reg
    let is_tombstone = function
      | Tombstone -> true
      | _ -> false
    let tombstone = Tombstone
    let of_operand = function
      | Reg r -> Some r
      | _ -> None
    let to_operand r = Reg r
    let compare r1 r2 = Int.compare (index r1) (index r2)
    let reg = function
      | Virtual v -> v.reg
      | r -> r
  end
  module RegSet = Set.Make (Reg)
  module RegMap = Map.Make (Reg)
  let is_tombstone = function
    | Reg Tombstone -> true
    | _ -> false

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
      let pp_operands = Format.pp_print_list ~pp_sep pp_operand in
      Format.fprintf fmt "%s %a" i.instr pp_operands (i.defs @ i.uses)
  let show_instr = Format.asprintf "%a" pp_instr

  let srcs i = i.uses
  let dests i = i.defs
  let map_uses f i =
    {
      i with
      uses = List.map (fun op -> if is_tombstone op then op else f op) i.uses;
    }
  let map_defs f i =
    {
      i with
      defs = List.map (fun op -> if is_tombstone op then op else f op) i.defs;
    }
  let rec regset_of_operand = function
    | Label (_, args) ->
      args
      |> List.filter (fun n -> not (is_tombstone n))
      |> List.fold_left
           (fun acc o -> RegSet.union acc (regset_of_operand o))
           RegSet.empty
    | Reg reg ->
      if Reg.is_tombstone reg then RegSet.empty else RegSet.singleton reg
    | _ -> RegSet.empty

  let uses instr =
    srcs instr |> List.map regset_of_operand
    |> List.fold_left RegSet.union RegSet.empty
  let defs instr =
    dests instr |> List.map regset_of_operand
    |> List.fold_left RegSet.union RegSet.empty

  type cond = Instruction.Cond.t [@@deriving show, eq]
  let constrained physical_reg = function
    | Physical p ->
      if p <> physical_reg then
        failwith "constrained: physical registers conflict"
      else Physical p
    | Virtual v ->
      v.reg_constr <- UsePhysical physical_reg;
      Virtual v
    | Tombstone -> failwith "constrained: got tombstone"
  let reuse reg = function
    | Physical _ -> failwith "reuse: expected virtual register"
    | Virtual v ->
      v.reg_constr <- ReuseOperand reg;
      Virtual v
    | Tombstone -> failwith "reuse: got tombstone"
  let reuse_op op dest =
    match (op, dest) with
    | Reg reg, Reg dest -> Reg (reuse reg dest)
    | _ -> failwith "reuse_op: expected register"
  let goto l ops = { instr = "j"; defs = []; uses = [ Label (l, ops) ] }
  let cbranch ~args cond l1 l1args l2 l2args =
    {
      instr = Format.asprintf "cmp %a" Instruction.Cond.pp cond;
      uses = args @ [ Label (l1, l1args); Label (l2, l2args) ];
      defs = [];
    }
  let return ~uses = { instr = "ret"; uses; defs = [] }
  let instr instr ~defs ~uses = { instr; defs; uses }
  let mov ~dest ~src = instr "movq" ~defs:[ dest ] ~uses:[ src ]
  let pcopy ~dests ~srcs = instr "pcopy" ~defs:dests ~uses:srcs
  let is_side_effectful _ = true
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
  let int_regs =
    [
      rax;
      rbx;
      rcx;
      rdx;
      rsi;
      rdi;
      rsp;
      rbp;
      r8;
      r9;
      r10;
      r11;
      r12;
      r13;
      r14;
      r15;
    ]
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
module Writer = struct
  type label = Cfg.label
  let rec pp_reg fmt = function
    | Target.Physical (_, _, s) -> Format.fprintf fmt "%s" s
    | Virtual v ->
      begin match v.reg with
      | Physical _ as r -> Format.fprintf fmt "%a" pp_reg r
      | _ ->
        failwith
        @@ Format.asprintf "Uncolored virtual register %d%a%a" v.id
             Target.pp_reg_class v.reg_class Target.pp_reg_constr v.reg_constr
      end
    | Tombstone -> ()
  let pp_operand fmt = function
    | Target.Label (l, _) -> Format.fprintf fmt "%s" (snd l)
    | op -> Target.pp_operand' pp_reg fmt op
  let pp_instr fmt i =
    let pp_operands = Format.pp_print_list ~pp_sep:Target.pp_sep pp_operand in
    Format.fprintf fmt "%s %a" i.Target.instr pp_operands (i.defs @ i.uses)
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
    | Label (l, _info) -> Format.fprintf fmt "%a:" pp_label l
  let pp_middle fmt (Instruction instr) = Format.fprintf fmt "%a" pp_instr instr
  let pp_last fmt = function
    | Exit | Return _ -> Format.fprintf fmt "ret"
    | Branch (i, _) | CBranch (i, _, _) -> Format.fprintf fmt "%a" pp_instr i

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

module Deadcode = Deadcode.Make (Target) (Cfg) (Flow)
module ExecfreqRequirements :
  Execfreq.Requirements with module Target = Target = struct
  module Target = Target
  let instr_name = fun i -> i.Target.instr
  let imm = function
    | Target.Imm i -> Some i
    | _ -> None
  let label = function
    | Target.Label (l, _) -> Some l
    | _ -> None
  let uses = fun i -> i.Target.uses
  let call = "call"
  let ret = "ret"
  let cmp = "cmp"
  let exit = "exit"
end
module SeqpcopyRequirements :
  Seqpcopy.Requirements with module Target = Target = struct
  module Target = Target
  let temp = Target.Reg (Target.Physical Regs.r8)
  let is_pcopy instr = instr.Target.instr = "pcopy"
  let mov = Target.mov
  let uses instr = List.map Target.to_colored instr.Target.uses
  let defs instr = List.map Target.to_colored instr.Target.defs
end
