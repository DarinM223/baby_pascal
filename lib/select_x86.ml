open X86
module NameHashtbl = Hashtbl.Make (struct
  include Normalize.Name
  let equal = equal
  let hash = Hashtbl.hash
end)
module IntHashtbl = Utils.IntHashtbl

let ( let* ) = ( @@ )
let hashtbl_size = 100

module State = struct
  type t = {
    fresh_vreg : Target.reg_class -> Target.reg;
    mapping : Target.operand NameHashtbl.t;
    curr_block : Cfg.uid ref;
    vreg_block : Cfg.uid IntHashtbl.t;
    stack_offset : int ref;
    new_stack_slot : int -> Target.operand;
  }

  let init () =
    let curr_block = ref Cfg.entry_uid in
    let vreg_block = IntHashtbl.create hashtbl_size in
    let fresh_vreg =
      let c = ref (-1) in
      fun clz ->
        incr c;
        IntHashtbl.replace vreg_block !c !curr_block;
        let rec reg =
          Target.Virtual { id = !c; reg_class = clz; reg; reg_constr = Any }
        in
        reg
    in
    let stack_offset = ref 0 in
    let mapping = NameHashtbl.create hashtbl_size in
    let new_stack_slot size =
      let slot = !stack_offset in
      stack_offset := !stack_offset + size;
      Target.StackSlot slot
    in
    {
      fresh_vreg;
      mapping;
      curr_block;
      vreg_block;
      stack_offset;
      new_stack_slot;
    }

  let assign_vreg { fresh_vreg; mapping; _ } clz = function
    | Undag.Target.Reg n ->
      let vreg = fresh_vreg clz in
      NameHashtbl.add mapping n (Reg vreg);
      vreg
    | _ -> failwith "assign_vreg: expected destination to be register"
end

let call_conv_int { State.fresh_vreg; new_stack_slot; _ } = function
  | 0 -> Target.(Reg (constrained Regs.rdi (fresh_vreg Int)))
  | 1 -> Target.(Reg (constrained Regs.rsi (fresh_vreg Int)))
  | 2 -> Target.(Reg (constrained Regs.rdx (fresh_vreg Int)))
  | 3 -> Target.(Reg (constrained Regs.rcx (fresh_vreg Int)))
  | 4 -> Target.(Reg (constrained Regs.r8 (fresh_vreg Int)))
  | 5 -> Target.(Reg (constrained Regs.r9 (fresh_vreg Int)))
  | _ -> new_stack_slot 8

let rec select ({ State.fresh_vreg; mapping; _ } as state)
    (instruction : Undag.Target.instr) (k : Target.operand -> Cfg.tail) :
    Cfg.tail =
  let assign_vreg clz reg = Target.Reg (State.assign_vreg state clz reg) in
  let rec translate_operand :
      Undag.Target.operand -> (Target.operand -> 'a) -> 'a = function
    | Undag.Target.Instr src -> select state src
    | Undag.Target.Const i -> fun k -> k (Target.Imm i)
    | Undag.Target.Reg r -> fun k -> k (NameHashtbl.find mapping r)
    | Undag.Target.Label (l, args) ->
      fun k -> translate_operands args (fun args -> k (Target.Label (l, args)))
  and translate_operands l k =
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
    let* f = translate_operand f in
    let f =
      match f with
      | Label (l, []) -> l
      | _ -> failwith "call: expected function to be label"
    in
    let* args = translate_operands args in
    let dests = List.(init (length args) (call_conv_int state)) in
    let clobbered =
      List.map (fun r -> Reg (constrained r (fresh_vreg Int))) Regs.caller_save
    in
    let dests = List.append dests clobbered in
    let rax =
      List.find
        (function
          | Reg (Virtual { reg_constr = UsePhysical r; _ }) when r = Regs.rax ->
            true
          | _ -> false)
        clobbered
    in
    pcopy ~dests ~srcs:args
    @> instr "call" ~defs:[] ~uses:[ Label (f, []) ]
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

let codegen_block state ((first, tail) : Undag.Cfg.block) : Cfg.block =
  let first =
    match first with
    | Undag.Cfg.Entry -> Cfg.Entry
    | Undag.Cfg.Label (l, i) ->
      let map_vreg n = State.assign_vreg state Target.Int (Reg n) in
      Cfg.Label (l, { local = i.local; args = List.map map_vreg i.args })
  in
  let endd = Cfg.Last Cfg.Exit in
  let rec go_tail (tail : Undag.Cfg.tail) : Cfg.tail =
    match tail with
    | Undag.Cfg.Last last ->
      begin match last with
      | Undag.Cfg.Exit -> endd
      | Undag.Cfg.Branch (i, _) -> select state i (Fun.const endd)
      | Undag.Cfg.CBranch (i, _, _) -> select state i (Fun.const endd)
      | Undag.Cfg.Return i -> select state i (Fun.const endd)
      end
    | Undag.Cfg.Tail (Instruction i, rest) ->
      select state i (fun _ -> go_tail rest)
  in
  let tail = go_tail tail in
  (first, tail)

let codegen_function ?(args = []) (state : State.t) (graph : Undag.Cfg.graph) :
    Target.operand list * Cfg.graph =
  let srcs = List.init (List.length args) (call_conv_int state) in
  let dests =
    List.map
      (fun arg -> Target.Reg (State.assign_vreg state Int (Reg arg)))
      args
  in
  let pcopy = X86.Cfg.Instruction (Target.pcopy ~dests ~srcs) in
  let graph =
    List.fold_left
      (fun acc block ->
        state.curr_block := Undag.Cfg.id block;
        X86.Cfg.Blocks.insert (codegen_block state block) acc)
      X86.Cfg.empty
      (Undag.Cfg.reverse_postorder_dfs graph)
  in
  let zblock, graph = X86.Cfg.focus_entry graph in
  match zblock with
  | First Entry, tail when List.length args > 0 ->
    (srcs, X86.Cfg.unfocus ((First Entry, Tail (pcopy, tail)), graph))
  | _ -> (srcs, X86.Cfg.unfocus (zblock, graph))

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

let%expect_test "Fibonacci code generation" =
  let cfg = Examples.fibonacci in
  let _, cfg = codegen_test_helper ~args:[ "v" ] (State.init ()) cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      pcopy [(%1any, %0(%rdi))]
      jle label2, label3, %1any, $1
    label1(local=false)(32any):
      movq %33(%rax), %32any
      ret %33(%rax)
    label2(local=false)():
      movq %2any, %1any
      jmp label1(%2any)
    label3(local=false)():
      movq %5any, %1any
      subq %4(reuse=%5), %5any, $1
      pcopy [(%6(%rdi), %4(reuse=%5)); (%7(%rax), %); (%8(%rcx), %);
              (%9(%rdx), %); (%10(%rsi), %); (%11(%rdi), %); (%12(%r8), %);
              (%13(%r9), %); (%14(%r10), %); (%15(%r11), %)]
      call fibonacci
      movq %3any, %7(%rax)
      movq %18any, %1any
      subq %17(reuse=%18), %18any, $2
      pcopy [(%19(%rdi), %17(reuse=%18)); (%20(%rax), %); (%21(%rcx), %);
              (%22(%rdx), %); (%23(%rsi), %); (%24(%rdi), %); (%25(%r8), %);
              (%26(%r9), %); (%27(%r10), %); (%28(%r11), %)]
      call fibonacci
      movq %16any, %20(%rax)
      movq %31any, %3any
      addq %30(reuse=%31), %31any, %16any
      movq %29any, %30(reuse=%31)
      jmp label1(%29any)
    |}]

let%expect_test "Nested loops code generation" =
  let cfg = Examples.nested_loops in
  let _, cfg = codegen_test_helper (State.init ()) cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      movq %0any, $0
      jmp label6
    label1(local=false)():
      exit
    label2(local=false)(1any):
      jl label3, label1, %1any, $100
    label3(local=false)():
      movq %2any, %1any
      jmp label4(%1any, %2any)
    label4(local=false)(3any, 4any):
      jl label5, label2(%3any), %4any, $100
    label5(local=false)():
      movq %7any, %3any
      addq %6(reuse=%7), %7any, $1
      movq %5any, %6(reuse=%7)
      movq %10any, %4any
      addq %9(reuse=%10), %10any, $1
      movq %8any, %9(reuse=%10)
      jmp label4(%5any, %8any)
    label6(local=false)():
      jmp label2(%0any)
    |}]
