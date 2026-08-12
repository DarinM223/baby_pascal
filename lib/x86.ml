module Target = struct
  type label = Normalize.Target.label [@@deriving show, eq]
  type reg_class =
    | Int
    | Float
  [@@deriving eq]
  let pp_reg_class fmt = function
    | Int -> Format.fprintf fmt ""
    | Float -> Format.fprintf fmt "f"

  type physical_reg = int * reg_class * string [@@deriving eq]
  let pp_physical_reg fmt (_, _, s) = Format.fprintf fmt "%s" s
  let show_physical_reg phys = Format.asprintf "%a" pp_physical_reg phys

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
  let show_reg_class = Format.asprintf "%a" pp_reg_class
  let rec pp_reg_constr fmt = function
    | Any -> Format.fprintf fmt "any"
    | OnReg -> Format.fprintf fmt "reg"
    | OnStack -> Format.fprintf fmt "stack"
    | UsePhysical r -> Format.fprintf fmt "(%%%a)" pp_reg (Physical r)
    | ReuseOperand r -> Format.fprintf fmt "(reuse=%%%d)" r.id

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
  let equal_reg r1 r2 =
    match (r1, r2) with
    | Physical (id1, _, _), Physical (id2, _, _) -> id1 = id2
    | Virtual v1, Virtual v2 -> v1.id = v2.id
    | _ -> false

  type regs = reg list [@@deriving show, eq]
  type operand =
    | Imm of int
    | Reg of reg
    | MemAddr of {
        base : reg option;
        index : reg;
        scale : int;
        displacement : int;
      }
    | StackSlot of {
        relative_to_base : bool;
            (** if true, then offset is added to base pointer (the original
                stack pointer) instead of the current stack pointer *)
        offset : int;
      }
    | Label of label * operand list
  [@@deriving eq]
  let pp_sep fmt () = Format.fprintf fmt ", "
  let rec pp_operand' pp_reg fmt = function
    | Imm i -> Format.fprintf fmt "$%d" i
    | Reg r -> Format.fprintf fmt "%%%a" pp_reg r
    | MemAddr { displacement = 0; base = Some base; scale = 0; _ } ->
      Format.fprintf fmt "(%%%a)" pp_reg base
    | MemAddr { displacement; base = Some base; scale = 0; _ } ->
      Format.fprintf fmt "%d(%%%a)" displacement pp_reg base
    | MemAddr { displacement = 0; base; scale; index } ->
      Format.fprintf fmt "(%%%a,%%%a,%d)"
        (Format.pp_print_option pp_reg)
        base pp_reg index scale
    | MemAddr { displacement; base; index; scale } ->
      Format.fprintf fmt "%d(%%%a,%%%a,%d)" displacement
        (Format.pp_print_option pp_reg)
        base pp_reg index scale
    | StackSlot { offset; _ } -> Format.fprintf fmt "%d(%%rsp)" offset
    | Label (l, []) -> Format.fprintf fmt "%s" (snd l)
    | Label (l, args) ->
      Format.fprintf fmt "%s(%a)" (snd l)
        (Format.pp_print_list ~pp_sep (pp_operand' pp_reg))
        args
  let pp_operand = pp_operand' pp_reg
  let show_operand = Format.asprintf "%a" (pp_operand' pp_reg)
  let reg reg = Reg reg
  let destruct_reg = function
    | Reg r -> Some r
    | _ -> None
  let label label args = Label (label, args)
  let destruct_label = function
    | Label (l, args) -> Some (l, args)
    | _ -> None
  let rec fold_reg_operand (f : 'a -> reg -> 'a * reg) (acc : 'a) = function
    | Reg r ->
      let acc, r = f acc r in
      (acc, Reg r)
    | MemAddr ({ base : reg option; index : reg; _ } as addr) ->
      let acc, base =
        Option.fold ~none:(acc, base)
          ~some:(fun r -> CCPair.map_snd Option.some (f acc r))
          base
      in
      let acc, index = f acc index in
      (acc, MemAddr { addr with base; index })
    | Label (l, ops) ->
      let acc, ops = List.fold_left_map (fold_reg_operand f) acc ops in
      (acc, Label (l, ops))
    | (Imm _ | StackSlot _) as op -> (acc, op)
  let rec subst_reg_operand subst_reg = function
    | Reg r -> Reg (subst_reg r)
    | MemAddr ({ base : reg option; index : reg; _ } as addr) ->
      MemAddr
        { addr with base = Option.map subst_reg base; index = subst_reg index }
    | Label (l, ops) -> Label (l, List.map (subst_reg_operand subst_reg) ops)
    | (Imm _ | StackSlot _) as op -> op
  let to_colored =
    let to_colored_reg = function
      | Virtual { reg; _ } -> reg
      | reg -> reg
    in
    subst_reg_operand to_colored_reg

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
    let equal r1 r2 = Int.equal (index r1) (index r2)
    let compare r1 r2 = Int.compare (index r1) (index r2)
    let hash r = CCInt.hash (index r)
    let reg = function
      | Virtual v -> v.reg
      | r -> r
  end
  module RegSet = CCSet.Make (Reg)
  module RegMap = CCMap.Make (Reg)
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
  let is_pcopy instr = instr.instr = "pcopy"
  let pp_instr fmt i =
    if is_pcopy i then
      let pad_uses =
        List.append i.uses
          (List.init
             (List.length i.defs - List.length i.uses)
             (fun _ -> Reg Tombstone))
      in
      Format.fprintf fmt "pcopy %a" pp_pcopy (List.combine i.defs pad_uses)
    else
      let pp_operands = Format.pp_print_list ~pp_sep pp_operand in
      Format.fprintf fmt "%s %a" i.instr pp_operands (i.defs @ i.uses)
  let show_instr = Format.asprintf "%a" pp_instr

  let prepend_use op i = { i with uses = op :: i.uses }
  let prepend_def op i = { i with defs = op :: i.defs }

  let srcs i = i.uses
  let dests i = i.defs
  let fold_uses f init i =
    let res, uses =
      List.fold_left_map
        (fun acc op -> if is_tombstone op then (acc, op) else f acc op)
        init i.uses
    in
    (res, { i with uses })
  let map_uses f i = snd (fold_uses (fun _ op -> ((), f op)) () i)
  let map_reg_uses f = map_uses (subst_reg_operand f)
  let fold_reg_uses f = fold_uses (fold_reg_operand f)
  let fold_defs f init i =
    let res, defs =
      List.fold_left_map
        (fun acc op -> if is_tombstone op then (acc, op) else f acc op)
        init i.defs
    in
    (res, { i with defs })
  let map_defs f i = snd (fold_defs (fun _ op -> ((), f op)) () i)
  let fold_reg_defs f = fold_defs (fold_reg_operand f)

  let uses instr =
    fst
    @@ fold_reg_uses
         (fun acc reg -> (RegSet.add reg acc, reg))
         RegSet.empty instr
  let defs instr =
    fst
    @@ fold_reg_defs
         (fun acc reg -> (RegSet.add reg acc, reg))
         RegSet.empty instr

  type cond = Graph.Cond.t [@@deriving show, eq]
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
      begin match reg with
      | Virtual vreg -> v.reg_constr <- ReuseOperand vreg
      | _ -> ()
      end;
      Virtual v
    | Tombstone -> failwith "reuse: got tombstone"
  let reuse_op op dest =
    match (op, dest) with
    | Reg reg, Reg dest -> Reg (reuse reg dest)
    | _ -> failwith "reuse_op: expected register"
  let goto l ops = { instr = "jmp"; defs = []; uses = [ Label (l, ops) ] }
  let cond_mapping =
    Graph.Cond.
      [
        (LT, "jl"); (LE, "jle"); (GT, "jg"); (GE, "jge"); (EQ, "jz"); (NE, "jnz");
      ]

  let cbranch ~args cond l1 l1args l2 l2args =
    let jmp = snd @@ List.find (fun (c, _) -> cond = c) cond_mapping in
    {
      instr = jmp;
      uses = Label (l1, l1args) :: Label (l2, l2args) :: args;
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
  let callee_save = [ r12; r13; r14; r15; rbx; rsp; rbp ]
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
  let pp_operand (stack_offset, frame_pointer) fmt = function
    | Target.StackSlot { relative_to_base = true; offset } ->
      begin match frame_pointer with
      | Some reg -> Format.fprintf fmt "%d(%%%a)" offset Target.pp_reg reg
      | None ->
        Target.pp_operand' pp_reg fmt
          (Target.StackSlot
             { relative_to_base = false; offset = offset + stack_offset })
      end
    | Label (l, _) -> Format.fprintf fmt "%s" (snd l)
    | op -> Target.pp_operand' pp_reg fmt op
  let pp_instr state fmt i =
    let pp_operands =
      Format.pp_print_list ~pp_sep:Target.pp_sep (pp_operand state)
    in
    Format.fprintf fmt "%s %a" i.Target.instr pp_operands
      (List.filter (fun op -> not (Target.is_tombstone op)) (i.uses @ i.defs))
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
  let pp_middle state fmt (Instruction instr) =
    Format.fprintf fmt "%a" (pp_instr state) instr
  let pp_last state fmt = function
    | Exit | Return _ -> Format.fprintf fmt "ret"
    | Branch (i, _) | CBranch (i, _, _) ->
      Format.fprintf fmt "%a" (pp_instr state) i

  type head = Cfg.head =
    | First of first
    | Head of head * middle
  let rec pp_head state fmt = function
    | First f -> Format.fprintf fmt "%a@\n" pp_first f
    | Head (h, m) ->
      Format.fprintf fmt "%a  %a@\n" (pp_head state) h (pp_middle state) m
  type tail = Cfg.tail =
    | Last of last
    | Tail of middle * tail
  let rec pp_tail state fmt = function
    | Last l -> Format.fprintf fmt "%a@\n" (pp_last state) l
    | Tail (m, t) ->
      Format.fprintf fmt "%a@\n  %a" (pp_middle state) m (pp_tail state) t
  type block = first * tail
  let pp_block state fmt (f, t) =
    Format.fprintf fmt "%a@\n  %a" pp_first f (pp_tail state) t
  let pp_graph state fmt =
    Cfg.Blocks.iter (fun _ block ->
        Format.fprintf fmt "%a" (pp_block state) block)
end

module Deadcode = Deadcode.Make (Target) (Cfg) (Flow)
module ExecfreqRequirements :
  Execfreq.Requirements with module Target = Target = struct
  module Target = Target
  let instr_name = fun i -> i.Target.instr
  let imm = function
    | Target.Imm i -> Some i
    | _ -> None
  let uses = fun i -> i.Target.uses
  let call = "call"
  let ret = "ret"
  let cond_mapping = Target.cond_mapping
  let exit = "exit"
end
module SeqpcopyRequirements :
  Seqpcopy.Requirements with module Target = Target = struct
  module Target = Target
  let temp = Target.Reg (Target.Physical Regs.r10)
  let is_pcopy = Target.is_pcopy
  let mov = Target.mov
  let uses instr = List.map Target.to_colored instr.Target.uses
  let defs instr = List.map Target.to_colored instr.Target.defs
end
module Sequentialize = Seqpcopy.Make (Cfg) (SeqpcopyRequirements)
