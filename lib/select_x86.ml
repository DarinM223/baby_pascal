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
    | ReuseOperand of reg
  and virtual_reg = {
    id : int;
    reg_class : reg_class;
    mutable reg_constr : reg_constr;
  }
  and reg =
    | Physical of physical_reg
    | Virtual of virtual_reg
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
    | Label of label
  [@@deriving show, eq]
  type operands = operand list [@@deriving show, eq]
  type instr = {
    instr : string;
    defs : operands;
    uses : operands;
  }
  [@@deriving show, eq]
  type cond = Instruction.Cond.t
  let index = function
    | Physical (id, _) -> id
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
  let rax = (0, Target.Int)
  let rbx = (1, Target.Int)
  let rcx = (2, Target.Int)
  let rdx = (3, Target.Int)
  let rsi = (4, Target.Int)
  let rdi = (5, Target.Int)
  let rsp = (6, Target.Int)
  let rbp = (7, Target.Int)
  let r8 = (8, Target.Int)
  let r9 = (9, Target.Int)
end

module NameHashtbl = Hashtbl.Make (struct
  include Normalize.Name
  let equal = equal
  let hash = Hashtbl.hash
end)
module IntHashtbl = Hashtbl.Make (Int)
module Cfg = Graph.Make (Target)

let ( let* ) = ( @@ )
let hashtbl_size = 100

type state = {
  fresh_vreg : Target.reg_class -> Target.reg;
  mapping : Target.operand NameHashtbl.t;
  new_stack_slot : unit -> Target.operand;
}

let call_conv_int { fresh_vreg; new_stack_slot; _ } = function
  | 0 -> Target.(Reg (constrained Regs.rdi (fresh_vreg Int)))
  | 1 -> Target.(Reg (constrained Regs.rsi (fresh_vreg Int)))
  | 2 -> Target.(Reg (constrained Regs.rdx (fresh_vreg Int)))
  | 3 -> Target.(Reg (constrained Regs.rcx (fresh_vreg Int)))
  | 4 -> Target.(Reg (constrained Regs.r8 (fresh_vreg Int)))
  | 5 -> Target.(Reg (constrained Regs.r9 (fresh_vreg Int)))
  | _ -> new_stack_slot ()

let rec select ({ fresh_vreg; mapping; _ } as state)
    (instruction : Undag.Target.instr) (k : Target.operand -> Cfg.tail) :
    Cfg.tail =
  let assign_vreg clz = function
    | Undag.Target.Reg n ->
      let vreg = Target.Reg (fresh_vreg clz) in
      NameHashtbl.add mapping n vreg;
      vreg
    | _ -> failwith "assign_vreg: expected destination to be register"
  in
  let translate_operand : Undag.Target.operand -> (Target.operand -> 'a) -> 'a =
    function
    | Undag.Target.Instr src -> select state src
    | Undag.Target.Const i -> fun k -> k (Target.Imm i)
    | Undag.Target.Reg r -> fun k -> k (NameHashtbl.find mapping r)
    | Undag.Target.Label (l, _) -> fun k -> k (Target.Label l)
  in
  let translate_operands l k =
    let rec go acc l k =
      match l with
      | x :: xs ->
        let* x = translate_operand x in
        go (x :: acc) xs k
      | [] -> k (List.rev acc)
    in
    go [] l k
  in
  let ( @> ) i t = Cfg.Tail (Instruction i, t) in
  match instruction with
  | Undag.Target.Assign (dest, src) ->
    let open Target in
    let dest = assign_vreg Int dest in
    let* src = translate_operand src in
    mov ~dest ~src @> k dest
  | Undag.Target.Uop (dest, Not, src) ->
    let open Target in
    let dest = assign_vreg Int dest in
    let tmp = Reg (fresh_vreg Int) in
    let* src = translate_operand src in
    mov ~dest:tmp ~src:(Imm 0)
    @> instr "testq" ~defs:[] ~uses:[ src; src ]
    @> instr "setz" ~defs:[ reuse_op tmp dest ] ~uses:[ tmp ]
    @> k dest
  | Undag.Target.Bop (dest, bop, src1, src2) ->
    let open Target in
    let dest = assign_vreg Int dest in
    let* src1 = translate_operand src1 in
    let* src2 = translate_operand src2 in
    let reuse_bop i =
      let tmp = Reg (fresh_vreg Int) in
      mov ~dest:tmp ~src:src1
      @> instr i ~defs:[ reuse_op tmp dest ] ~uses:[ tmp; src2 ]
      @> k dest
    in
    let reuse_cond i =
      let tmp1 = Reg (fresh_vreg Int) in
      let tmp2 = Reg (fresh_vreg Int) in
      let tmp3 = Reg (fresh_vreg Int) in
      mov ~dest:tmp1 ~src:src1
      @> mov ~dest:tmp2 ~src:(Imm 0)
      @> instr "cmp" ~defs:[ reuse_op tmp1 tmp3 ] ~uses:[ tmp1; src2 ]
      @> instr i ~defs:[ reuse_op tmp2 dest ] ~uses:[ tmp2 ]
      @> k dest
    in
    begin match bop with
    | Ast.Add -> reuse_bop "addq"
    | Ast.Sub -> reuse_bop "subq"
    | Ast.Mul -> reuse_bop "mulq"
    | Ast.And ->
      let tmp = Reg (fresh_vreg Int) in
      mov ~dest:tmp ~src:src1
      @> instr "testq" ~defs:[] ~uses:[ tmp; tmp ]
      @> instr "cmovnz" ~defs:[ reuse_op tmp dest ] ~uses:[ tmp; src2 ]
      @> k dest
    | Ast.Or ->
      let tmp = Reg (fresh_vreg Int) in
      mov ~dest:tmp ~src:src1
      @> instr "testq" ~defs:[] ~uses:[ tmp; tmp ]
      @> instr "cmovz" ~defs:[ reuse_op tmp dest ] ~uses:[ tmp; src2 ]
      @> k dest
    | Ast.Eq -> reuse_cond "setz"
    | Ast.Neq -> reuse_cond "setnz"
    | Ast.Lt -> reuse_cond "setl"
    | Ast.Le -> reuse_cond "setle"
    | Ast.Gt -> reuse_cond "setg"
    | Ast.Ge -> reuse_cond "setge"
    end
  | Undag.Target.Return ops ->
    let* ops = translate_operands ops in
    begin match ops with
    | [] -> Cfg.Last (Cfg.Return (Target.return ~uses:[]))
    | [ op ] ->
      let rax = Target.(Reg (constrained Regs.rax (fresh_vreg Int))) in
      Target.instr "movq" ~defs:[ rax ] ~uses:[ op ]
      @> Cfg.Last (Cfg.Return (Target.return ~uses:[ rax ]))
    | _ -> failwith "can only return one thing currently"
    end
  | Undag.Target.Call (dest, f, args) ->
    let open Target in
    let dest = assign_vreg Int dest in
    let rax = Reg (constrained Regs.rax (fresh_vreg Int)) in
    let* f = translate_operand f in
    let f =
      match f with
      | Label l -> l
      | _ -> failwith "call: expected function to be label"
    in
    let* args = translate_operands args in
    let dests = List.(init (length args) (call_conv_int state)) in
    pcopy ~dests ~srcs:args
    (* todo: add caller save registers to call defs *)
    @> instr "call" ~defs:[] ~uses:[ Label f ]
    @> mov ~dest ~src:rax @> k dest
  | Undag.Target.Goto (l, args) ->
    let* args = translate_operands args in
    Cfg.Last (Cfg.Branch (Target.goto l args, l))
  | Undag.Target.Cbranch (src1, src2, cond, l1, l1args, l2, l2args) ->
    let* src1 = translate_operand src1 in
    let* src2 = translate_operand src2 in
    let* l1args = translate_operands l1args in
    let* l2args = translate_operands l2args in
    Cfg.Last
      (Cfg.CBranch
         (Target.cbranch ~args:[ src1; src2 ] cond l1 l1args l2 l2args, l1, l2))

let codegen_block ((first, tail) : Undag.Cfg.block) : Cfg.block =
  let fresh_vreg =
    let c = ref (-1) in
    fun clz ->
      incr c;
      Target.Virtual { id = !c; reg_class = clz; reg_constr = Any }
  in
  let mapping = NameHashtbl.create hashtbl_size in
  (* todo: implement this *)
  let new_stack_slot () = Target.StackSlot 0 in
  let state = { fresh_vreg; mapping; new_stack_slot } in
  let first =
    match first with
    | Undag.Cfg.Entry -> Cfg.Entry
    | Undag.Cfg.Label (l, i) ->
      let map_vreg n =
        let vreg = fresh_vreg Target.Int in
        NameHashtbl.add mapping n (Target.Reg vreg);
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
      | Undag.Cfg.Branch (i, _) -> select state i (Fun.const endd)
      | Undag.Cfg.CBranch (i, _, _) -> select state i (Fun.const endd)
      | Undag.Cfg.Return i -> select state i (Fun.const endd)
    end
    | Undag.Cfg.Tail (Instruction i, rest) ->
      select state i (Fun.const (go_tail rest))
  in
  let tail = go_tail tail in
  (first, tail)
