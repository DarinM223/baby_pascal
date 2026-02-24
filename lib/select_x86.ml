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
  let constrained physical_reg = function
    | Physical p ->
      if p <> physical_reg then
        failwith "constrained: physical registers conflict"
      else Physical p
    | Virtual (i, clz, _) -> Virtual (i, clz, UsePhysical physical_reg)
  let reuse idx = function
    | Physical _ -> failwith "reuse: expected virtual register"
    | Virtual (i, clz, _) -> Virtual (i, clz, ReuseOperand idx)
  let goto l ops = { instr = "j"; defs = []; uses = Block l :: ops }
  let cbranch ~args cond l1 l1args l2 l2args =
    {
      instr = Format.asprintf "cmp %a" Instruction.Cond.pp cond;
      uses = args @ [ Block l1 ] @ l1args @ [ Block l2 ] @ l2args;
      defs = [];
    }
  let return ~uses = { instr = "ret"; uses; defs = [] }
  let instr instr ~defs ~uses = { instr; defs; uses }
end

module Regs = struct
  let rax = (0, Target.Int)

  (* todo: handle overlapping registers *)
  let al = (1, Target.Int)
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
  let translate_operand : Undag.Target.operand -> (Target.operand -> 'a) -> 'a =
    function
    | Undag.Target.Instr src -> select fresh_vreg mapping src
    | Undag.Target.Const i -> fun k -> k (Target.Imm i)
    | Undag.Target.Reg r -> fun k -> k (Target.Reg (NameHashtbl.find mapping r))
    | Undag.Target.Label (l, _) -> fun k -> k (Target.Block l)
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
  match instr with
  | Undag.Target.Assign (dest, src) ->
    let dest = Target.(Reg (assign_vreg Int dest)) in
    let* src = translate_operand src in
    Target.instr "mov" ~defs:[ dest ] ~uses:[ src ] @> k dest
  | Undag.Target.Uop (dest, Not, src) ->
    let rax = Target.(Reg (constrained Regs.rax (fresh_vreg Int))) in
    let reuse = Target.(Reg (reuse 0 (fresh_vreg Int))) in
    let dest = Target.(Reg (constrained Regs.al (assign_vreg Int dest))) in
    let* src = translate_operand src in
    Target.instr "xorq" ~defs:[ reuse ] ~uses:[ rax; rax ]
    @> Target.instr "testq" ~defs:[] ~uses:[ src; src ]
    @> Target.instr "sete" ~defs:[ dest ] ~uses:[]
    @> k dest
  | Undag.Target.Bop (dest, bop, src1, src2) ->
    let dest = Target.(Reg (reuse 0 (assign_vreg Int dest))) in
    let* src1 = translate_operand src1 in
    let* src2 = translate_operand src2 in
    begin match bop with
    | Ast.Add ->
      Target.instr "addq" ~defs:[ dest ] ~uses:[ src1; src2 ] @> k dest
    | Ast.Sub ->
      Target.instr "subq" ~defs:[ dest ] ~uses:[ src1; src2 ] @> k dest
    | Ast.Mul ->
      Target.instr "mulq" ~defs:[ dest ] ~uses:[ src1; src2 ] @> k dest
    | Ast.And -> failwith ""
    | Ast.Or -> failwith ""
    | Ast.Eq -> failwith ""
    | Ast.Neq -> failwith ""
    | Ast.Lt -> failwith ""
    | Ast.Le -> failwith ""
    | Ast.Gt -> failwith ""
    | Ast.Ge -> failwith ""
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
  | Undag.Target.Call (_, _, _) -> failwith ""
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
