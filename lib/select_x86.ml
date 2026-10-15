open X86
module NameHashtbl = Normalize.NameHashtbl
module IntHashtbl = Utils.IntHashtbl

let ( let* ) = ( @@ )

module State = struct
  module Target = Target
  type t = {
    fresh_vreg : Target.reg_class -> Target.reg;
    mapping : Target.operand NameHashtbl.t;
    vreg_block : Cfg.uid IntHashtbl.t;
    new_stack_slot : int -> Target.operand;
    mutable curr_block : Cfg.uid;
    mutable stack_offset : int;
    mutable frame_pointer : Target.reg option;
  }

  let init () =
    let vreg_block = IntHashtbl.create Utils.hashtbl_size in
    let mapping = NameHashtbl.create Utils.hashtbl_size in
    let c = ref (-1) in
    let rec r =
      {
        fresh_vreg =
          (fun clz ->
            incr c;
            IntHashtbl.replace vreg_block !c r.curr_block;
            let rec reg =
              Target.Virtual { id = !c; reg_class = clz; reg; reg_constr = Any }
            in
            reg);
        mapping;
        vreg_block;
        new_stack_slot =
          (fun size ->
            let slot = r.stack_offset in
            r.stack_offset <- r.stack_offset + size;
            if Option.is_some r.frame_pointer then
              Target.StackSlot
                { relative_to_base = true; offset = -(slot + size) }
            else Target.StackSlot { relative_to_base = false; offset = slot });
        curr_block = Cfg.entry_uid;
        stack_offset = 0;
        frame_pointer = None;
      }
    in
    r

  let assign_vreg { fresh_vreg; mapping; _ } clz = function
    | Undag.Target.Reg (_, n) ->
      let vreg = fresh_vreg clz in
      NameHashtbl.add mapping n (Reg vreg);
      vreg
    | _ -> failwith "assign_vreg: expected destination to be register"
end

module Select = struct
  module G = X86.Cfg
  module State = State

  let reg_class_of_operand : Undag.Target.operand -> Target.reg_class = function
    | Undag.Target.Reg (Ast.TInteger, _) -> Target.Int
    | Reg (TDouble, _) -> Target.Float
    | _ -> Target.Int

  let call_conv ~caller { State.fresh_vreg; new_stack_slot; _ } = function
    | Target.Int ->
      begin function
        | 0 -> Target.(Reg (constrained Regs.rdi (fresh_vreg Int)))
        | 1 -> Target.(Reg (constrained Regs.rsi (fresh_vreg Int)))
        | 2 -> Target.(Reg (constrained Regs.rdx (fresh_vreg Int)))
        | 3 -> Target.(Reg (constrained Regs.rcx (fresh_vreg Int)))
        | 4 -> Target.(Reg (constrained Regs.r8 (fresh_vreg Int)))
        | 5 -> Target.(Reg (constrained Regs.r9 (fresh_vreg Int)))
        | n ->
          if caller then new_stack_slot 8
          else
            Target.StackSlot { relative_to_base = true; offset = (n - 5) * 8 }
      end
    | Target.Float ->
      begin function
        | 0 -> Target.(Reg (constrained Regs.xmm0 (fresh_vreg Float)))
        | 1 -> Target.(Reg (constrained Regs.xmm1 (fresh_vreg Float)))
        | 2 -> Target.(Reg (constrained Regs.xmm2 (fresh_vreg Float)))
        | 3 -> Target.(Reg (constrained Regs.xmm3 (fresh_vreg Float)))
        | 4 -> Target.(Reg (constrained Regs.xmm4 (fresh_vreg Float)))
        | 5 -> Target.(Reg (constrained Regs.xmm5 (fresh_vreg Float)))
        | 6 -> Target.(Reg (constrained Regs.xmm6 (fresh_vreg Float)))
        | 7 -> Target.(Reg (constrained Regs.xmm7 (fresh_vreg Float)))
        | n ->
          if caller then new_stack_slot 8
          else
            Target.StackSlot { relative_to_base = true; offset = (n - 7) * 8 }
      end

  let reuse_instr tmp dest instr =
    instr
    |> Target.modify_uses (fun ~uses ~num_hidden ->
        (tmp :: uses, num_hidden + 1))
    |> Target.modify_defs (fun ~defs ~num_hidden ->
        (Target.reuse_op tmp dest :: defs, num_hidden))
  let ( @> ) i t = Cfg.Tail (Instruction i, t)

  let reuse_cond fresh src1_class src1 src2_class src2 init k mk_instr =
    let open Target in
    let tmp1 = Reg (fresh src1_class) in
    let tmp2 = Reg (fresh src2_class) in
    let args, inject = init () in
    let setters =
      List.fold_right
        (fun (arg, tmp, dest) f t -> mk_instr arg tmp dest @> f t)
        args
        (fun t -> t)
    in
    mov ~dest:tmp1 ~src:src1 @> inject
    @@ reuse_instr tmp1 tmp2 (instr "cmp" ~defs:[] ~uses:[ src2 ])
    @> setters (k (List.map (fun (_, _, dest) -> dest) args))

  let rec select ({ State.fresh_vreg; mapping; _ } as state)
      (instruction : Undag.Target.instr) (k : Target.operand -> Cfg.tail) :
      Cfg.tail =
    let assign_vreg clz reg = Target.Reg (State.assign_vreg state clz reg) in
    let rec translate_operand :
        Undag.Target.operand -> (Target.operand -> 'a) -> 'a = function
      | Undag.Target.Instr src -> select state src
      | Undag.Target.Const i -> fun k -> k (Target.Imm i)
      | Undag.Target.Reg (_, r) ->
        fun k ->
          begin try k (NameHashtbl.find mapping r)
          with Not_found ->
            failwith
            @@ Format.asprintf
                 "Select_X86: Register %a not found in mapping %a in \
                  instruction %a\n"
                 Normalize.Name.pp r
                 (NameHashtbl.pp ~pp_sep:Utils.pp_sep Normalize.Name.pp
                    Target.pp_operand)
                 mapping Undag.Target.pp_instr instruction
          end
      | Undag.Target.Label (l, args) ->
        fun k ->
          translate_operands args (fun args -> k (Target.Label (l, args)))
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
    match instruction with
    | Undag.Target.Assign (dest, src) ->
      let open Target in
      let dest_class = reg_class_of_operand dest in
      let dest = assign_vreg dest_class dest in
      let* src = translate_operand src in
      begin match dest_class with
      | Int -> mov ~dest ~src @> k dest
      | Float -> instr "movsd" ~defs:[ dest ] ~uses:[ src ] @> k dest
      end
    | Undag.Target.Uop (dest, Not, src) ->
      let src_class = reg_class_of_operand src in
      let open Target in
      let dest = assign_vreg src_class dest in
      let tmp = Reg (fresh_vreg src_class) in
      let* src = translate_operand src in
      mov ~dest:tmp ~src:(Imm 0)
      @> instr "testq" ~defs:[] ~uses:[ src; src ]
      @> reuse_instr tmp dest (instr "setz" ~defs:[] ~uses:[])
      @> k dest
    | Undag.Target.Bop (dest, bop, src1, src2) ->
      let open Target in
      let src1_class = reg_class_of_operand src1 in
      let src2_class = reg_class_of_operand src2 in
      let dest = assign_vreg src1_class dest in
      let* src1 = translate_operand src1 in
      let* src2 = translate_operand src2 in
      let reuse_bop i =
        let tmp = Reg (fresh_vreg src1_class) in
        mov ~dest:tmp ~src:src1
        @> reuse_instr tmp dest (instr i ~defs:[] ~uses:[ src2 ])
        @> k dest
      in
      let instr_of_cond i _arg tmp dest =
        reuse_instr tmp dest (instr i ~defs:[] ~uses:[])
      in
      let reuse_cond =
        reuse_cond fresh_vreg src1_class src1 src2_class src2
          (fun () ->
            let tmp = Reg (fresh_vreg Int) in
            let dest = Reg (fresh_vreg Int) in
            ([ (Imm 0, tmp, dest) ], fun t -> mov ~dest:tmp ~src:(Imm 0) @> t))
          (function
            | [ dest ] -> k dest
            | dests ->
              failwith
              @@ Format.asprintf
                   "reuse_cond: expected single destination, got: %a"
                   (Format.pp_print_list Target.pp_operand)
                   dests)
      in
      begin match (src1_class, bop) with
      | Int, Ast.Add -> reuse_bop "addq"
      | Float, Ast.Add -> reuse_bop "addsd"
      | Int, Ast.Sub -> reuse_bop "subq"
      | Float, Ast.Sub -> reuse_bop "subsd"
      | Int, Ast.Mul ->
        let tmp1 = Reg (constrained Regs.rax (fresh_vreg Int)) in
        let tmp2 = Reg (fresh_vreg Int) in
        let tmp3 = Reg (constrained Regs.rdx (fresh_vreg Int)) in
        let tmp4 = Reg (constrained Regs.rax (fresh_vreg Int)) in
        (* rax -> rdx:rax *)
        let mul =
          instr "imulq" ~defs:[] ~uses:[ tmp2 ]
          |> Target.modify_uses (fun ~uses ~num_hidden ->
              (tmp1 :: uses, num_hidden + 1))
          |> Target.modify_defs (fun ~defs ~num_hidden ->
              (tmp3 :: tmp4 :: defs, num_hidden + 2))
        in
        mov ~dest:tmp2 ~src:src2
        @> with_clobber_regs
             (RegSet.of_list Regs.[ Physical rax; Physical rdx ])
             (pcopy ~dests:[ tmp1 ] ~srcs:[ src1 ])
        @> mul @> mov ~dest ~src:tmp4 @> k dest
      | Int, Ast.Div ->
        let tmp1 = Reg (constrained Regs.rax (fresh_vreg Int)) in
        let tmp2 = Reg (fresh_vreg Int) in
        let tmp3 = Reg (constrained Regs.rdx (fresh_vreg Int)) in
        let tmp4 = Reg (constrained Regs.rax (fresh_vreg Int)) in
        let tmp5 = Reg (constrained Regs.rax (fresh_vreg Int)) in
        (* rax -> rdx:rax *)
        let cqto =
          instr "cqto" ~defs:[] ~uses:[]
          |> Target.modify_uses (fun ~uses ~num_hidden ->
              (tmp1 :: uses, num_hidden + 1))
          |> Target.modify_defs (fun ~defs ~num_hidden ->
              (tmp3 :: tmp4 :: defs, num_hidden + 2))
        in
        (* rdx:rax -> rax *)
        let div =
          instr "idivq" ~defs:[] ~uses:[ tmp2 ]
          |> Target.modify_uses (fun ~uses ~num_hidden ->
              (tmp3 :: tmp4 :: uses, num_hidden + 2))
          |> Target.modify_defs (fun ~defs ~num_hidden ->
              (tmp5 :: defs, num_hidden + 1))
        in
        (* Clobbers rax and rdx because of the cqto instruction *)
        mov ~dest:tmp2 ~src:src2
        @> with_clobber_regs
             (RegSet.of_list Regs.[ Physical rax; Physical rdx ])
             (pcopy ~dests:[ tmp1 ] ~srcs:[ src1 ])
        @> cqto @> div @> mov ~dest ~src:tmp5 @> k dest
      | Int, Ast.And ->
        (* todo: change to use bitwise and since we use that in value numbering *)
        let tmp = Reg (fresh_vreg Int) in
        mov ~dest:tmp ~src:src1
        @> instr "testq" ~defs:[] ~uses:[ tmp; tmp ]
        @> reuse_instr tmp dest (instr "cmovnz" ~defs:[] ~uses:[ src2 ])
        @> k dest
      | Int, Ast.Or ->
        (* todo: change to use bitwise or since we use that in value numbering *)
        let tmp = Reg (fresh_vreg Int) in
        mov ~dest:tmp ~src:src1
        @> instr "testq" ~defs:[] ~uses:[ tmp; tmp ]
        @> reuse_instr tmp dest (instr "cmovz" ~defs:[] ~uses:[ src2 ])
        @> k dest
      | Int, Ast.Eq -> reuse_cond (instr_of_cond "setz")
      | Int, Ast.Neq -> reuse_cond (instr_of_cond "setnz")
      | Int, Ast.Lt -> reuse_cond (instr_of_cond "setl")
      | Int, Ast.Le -> reuse_cond (instr_of_cond "setle")
      | Int, Ast.Gt -> reuse_cond (instr_of_cond "setg")
      | Int, Ast.Ge -> reuse_cond (instr_of_cond "setge")
      | Float, op ->
        failwith
        @@ Format.asprintf "Floating point operator for %a not implemented yet"
             Ast.pp_bop op
      end
    | Undag.Target.Return ops ->
      let* ops = translate_operands ops in
      begin match ops with
      | [] -> Cfg.Last (Cfg.Return (Target.return ~uses:[]))
      | [ op ] ->
        let rax = Target.(Reg (constrained Regs.rax (fresh_vreg Int))) in
        Target.pcopy ~dests:[ rax ] ~srcs:[ op ]
        @> Cfg.Last (Cfg.Return (Target.return ~uses:[ rax ]))
      | _ -> failwith "can only return one thing currently"
      end
    | Undag.Target.Call (dest, f, args) ->
      let open Target in
      let dest_class = reg_class_of_operand dest in
      let dest = assign_vreg dest_class dest in
      let* f = translate_operand f in
      let f =
        match f with
        | Label (l, []) -> l
        | _ -> failwith "call: expected function to be label"
      in
      let* args = translate_operands args in
      let dests =
        List.(init (length args) (call_conv ~caller:true state Target.Int))
      in
      let clobbered =
        let ints =
          List.map
            (fun r -> Reg (constrained r (fresh_vreg Int)))
            Regs.caller_save
        in
        let floats =
          List.map
            (fun r -> Reg (constrained r (fresh_vreg Float)))
            Regs.float_regs
        in
        ints @ floats
      in
      let rax =
        List.find
          (function
            | Reg (Virtual { reg_constr = UsePhysical r; _ }) when r = Regs.rax
              ->
              true
            | _ -> false)
          clobbered
      in
      let xmm0 =
        List.find
          (function
            | Reg (Virtual { reg_constr = UsePhysical r; _ }) when r = Regs.xmm0
              ->
              true
            | _ -> false)
          clobbered
      in
      let call =
        instr "call" ~defs:[] ~uses:[ Label (f, []) ]
        |> Target.modify_uses (fun ~uses ~num_hidden ->
            (dests @ uses, num_hidden + List.length dests))
        |> Target.modify_defs (fun ~defs ~num_hidden ->
            (clobbered @ defs, num_hidden + List.length clobbered))
      in
      let mov_instr =
        match dest_class with
        | Int -> Target.mov ~dest ~src:rax
        | Float -> Target.instr "movsd" ~defs:[ dest ] ~uses:[ xmm0 ]
      in
      with_clobber_regs
        (Regs.caller_save |> List.map (fun r -> Physical r) |> RegSet.of_list)
        (pcopy ~dests ~srcs:args)
      @> call @> mov_instr @> k dest
    | Undag.Target.Goto (l, args) ->
      let* args = translate_operands args in
      Cfg.Last (Cfg.Branch (Target.goto l args, l))
    | Undag.Target.Cbranch (src1, src2, cond, l1, l1args, l2, l2args) ->
      let src1_class = reg_class_of_operand src1 in
      let src2_class = reg_class_of_operand src2 in
      let* src1 = translate_operand src1 in
      let* src2 = translate_operand src2 in
      let* l1args = translate_operands l1args in
      let* l2args = translate_operands l2args in
      (* handle cbranches with the same label but different arguments *)
      if
        Cfg.equal_label l1 l2
        && not (List.equal Target.equal_operand l1args l2args)
      then
        let cmov arg1 _arg2 dest =
          Target.instr ~defs:[ dest ] ~uses:[ arg1 ]
            (match cond with
            | Graph.Cond.LT -> "cmovl"
            | LE -> "cmovle"
            | GT -> "cmovg"
            | GE -> "cmovge"
            | EQ -> "cmove"
            | NE -> "cmovne")
        in
        reuse_cond fresh_vreg src1_class src1 src2_class src2
          (fun () ->
            let open Target in
            let args =
              List.map
                (fun (arg1, arg2) ->
                  let dest = Reg (fresh_vreg Int) in
                  (arg1, arg2, dest))
                (List.combine l1args l2args)
            in
            ( args,
              List.fold_right
                (fun (_, arg2, dest) f t -> mov ~dest ~src:arg2 @> f t)
                args
                (fun t -> t) ))
          (fun dests -> Cfg.Last (Cfg.Branch (Target.goto l1 dests, l1)))
          cmov
      else
        Cfg.Last
          (Cfg.CBranch
             ( Target.cbranch ~args:[ src1; src2 ] cond l1 l1args l2 l2args,
               l1,
               l2 ))
    | Undag.Target.Alloca (dest, size) ->
      let open Target in
      let dest = assign_vreg Int dest in
      (* lea (use)slot, (def)reg *)
      if state.curr_block <> X86.Cfg.entry_uid then begin
        state.frame_pointer <- Some (Physical Regs.rbp);
        let rsp_address =
          MemAddr
            {
              base = Some (Physical Regs.rsp);
              index = Physical Regs.rsp;
              scale = 0;
              displacement = 0;
            }
        in
        (* for dynamic allocas, you need to manually increase the stack *)
        instr "subq" ~defs:[ Reg (Physical Regs.rsp) ] ~uses:[ Imm size ]
        @> instr "lea" ~defs:[ dest ] ~uses:[ rsp_address ]
        @> k dest
      end
      else begin
        (* alloca in entry block, so use it as a stack slot *)
        let slot = state.new_stack_slot size in
        instr "lea" ~defs:[ dest ] ~uses:[ slot ] @> k dest
      end
    | Undag.Target.Load (dest, src) ->
      let dest = assign_vreg (reg_class_of_operand dest) dest in
      let* src = translate_operand src in
      begin match src with
      | Reg reg ->
        let src =
          Target.MemAddr
            { base = Some reg; displacement = 0; scale = 0; index = reg }
        in
        Target.mov ~dest ~src @> k dest
      | _ -> failwith "Select_X86: expected source of load to be a register"
      end
    | Undag.Target.Store (dest, value) ->
      let* dest = translate_operand dest in
      let* value = translate_operand value in
      begin match dest with
      | Reg reg ->
        let dest =
          Target.MemAddr
            { base = Some reg; displacement = 0; scale = 0; index = reg }
        in
        Target.mov ~dest ~src:value @> k (Imm 0)
      | _ ->
        failwith "Select_X86: expected destination of store to be a register"
      end
    | Undag.Target.GetElementPtr _ ->
      failwith "Select_X86: GetElementPtr should have already been lowered"
end

include Isa.Codegen (Target) (X86.Cfg) (Select)

let%expect_test "Fibonacci code generation" =
  let cfg = Examples.fibonacci in
  let _, cfg =
    codegen_test_helper ~args:[ (TInteger, "v") ] (State.init ()) cfg
  in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      pcopy [(%1any, %0(%rdi))]
      jle label2, label3, %1any, $1
    label1(local=false)(64any):
      pcopy [(%65(%rax), %64any)]
      ret %65(%rax)
    label2(local=false)():
      movq %2any, %1any
      jmp label1(%2any)
    label3(local=false)():
      movq %5any, %1any
      subq %4(reuse=%5), %5any, $1
      pcopy [(%6(%rdi), %4(reuse=%5))]
      call %7(%rax), %8(%rcx), %9(%rdx), %10(%rsi), %11(%rdi), %12(%r8), %13(%r9), %14(%r10), %15(%r11), %16f(%xmm0), %17f(%xmm1), %18f(%xmm2), %19f(%xmm3), %20f(%xmm4), %21f(%xmm5), %22f(%xmm6), %23f(%xmm7), %24f(%xmm8), %25f(%xmm9), %26f(%xmm10), %27f(%xmm11), %28f(%xmm12), %29f(%xmm13), %30f(%xmm14), %31f(%xmm15), %6(%rdi), fibonacci
      movq %3any, %7(%rax)
      movq %34any, %1any
      subq %33(reuse=%34), %34any, $2
      pcopy [(%35(%rdi), %33(reuse=%34))]
      call %36(%rax), %37(%rcx), %38(%rdx), %39(%rsi), %40(%rdi), %41(%r8), %42(%r9), %43(%r10), %44(%r11), %45f(%xmm0), %46f(%xmm1), %47f(%xmm2), %48f(%xmm3), %49f(%xmm4), %50f(%xmm5), %51f(%xmm6), %52f(%xmm7), %53f(%xmm8), %54f(%xmm9), %55f(%xmm10), %56f(%xmm11), %57f(%xmm12), %58f(%xmm13), %59f(%xmm14), %60f(%xmm15), %35(%rdi), fibonacci
      movq %32any, %36(%rax)
      movq %63any, %3any
      addq %62(reuse=%63), %63any, %32any
      movq %61any, %62(reuse=%63)
      jmp label1(%61any)
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

let%expect_test "CBranch with both labels the same with different arguments" =
  let cfg = Examples.cbranch_same_label in
  let cfg = Undag.undag_graph cfg in
  let _, cfg = codegen_function ~args:[] (State.init ()) cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      movq %0any, $3
      movq %1any, $2
      movq %2any, $1
      movq %3any, $0
      jmp label1
    label1(local=false)():
      movq %4any, %3any
      movq %6any, %3any
      movq %7any, $2
      movq %8any, %0any
      cmp %5(reuse=%4), %4any, %2any
      cmove %6any, $1
      cmove %7any, %2any
      cmove %8any, %1any
      jmp label2(%6any, %7any, %8any)
    label2(local=false)(9any, 10any, 11any):
      exit
  |}]
