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
    let c = ref Regs.start_virtual_counter in
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

  let rec reg_class_of_operand : Undag.Target.operand -> Target.reg_class =
    let reg_class_of_type = function
      | Ast.TDouble -> Target.Float
      | _ -> Target.Int
    in
    function
    | Undag.Target.Reg (typ, _) -> reg_class_of_type typ
    | Label (typ, _, _) -> reg_class_of_type typ
    | Instr instr ->
      let reg_class =
        fst
        @@ Undag.Target.fold_defs
             (fun acc op ->
               if reg_class_of_operand op = Float then (Target.Float, op)
               else (acc, op))
             Target.Int instr
      in
      reg_class
    | Const _ -> Int

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
    @@ reuse_instr tmp1 tmp2
         (match src1_class with
         | Int -> instr "cmp" ~defs:[] ~uses:[ src2 ]
         | Float -> instr "ucomisd" ~defs:[] ~uses:[ src2 ])
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
      | Undag.Target.Label (typ, l, args) ->
        fun k ->
          translate_operands args (fun args -> k (Target.label typ l args))
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
    | Undag.Target.Assign (dest, (Label (Ast.TArray _, _, _) as src)) ->
      let open Target in
      let dest_class = reg_class_of_operand dest in
      let dest = assign_vreg dest_class dest in
      let* src = translate_operand src in
      instr "leaq" ~defs:[ dest ] ~uses:[ src ] @> k dest
    | Undag.Target.Assign (dest, src) ->
      let open Target in
      let dest_class = reg_class_of_operand dest in
      let dest = assign_vreg dest_class dest in
      let* src = translate_operand src in
      mov ~dest ~src @> k dest
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
      | Float, Ast.Mul -> reuse_bop "mulsd"
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
      | Float, Ast.Div -> reuse_bop "divsd"
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
      let ops_classes = List.map reg_class_of_operand ops in
      let* ops = translate_operands ops in
      begin match List.combine ops_classes ops with
      | [] -> Cfg.Last (Cfg.Return (Target.return ~uses:[]))
      | [ (op_class, op) ] ->
        begin match op_class with
        | Int ->
          let rax = Target.(Reg (constrained Regs.rax (fresh_vreg Int))) in
          Target.pcopy ~dests:[ rax ] ~srcs:[ op ]
          @> Cfg.Last (Cfg.Return (Target.return ~uses:[ rax ]))
        | Float ->
          let xmm0 = Target.(Reg (constrained Regs.xmm0 (fresh_vreg Float))) in
          Target.pcopy ~dests:[ xmm0 ] ~srcs:[ op ]
          @> Cfg.Last (Cfg.Return (Target.return ~uses:[ xmm0 ]))
        end
      | _ -> failwith "can only return one thing currently"
      end
    | Undag.Target.Call (dest, f, args) ->
      let open Target in
      let dest_class = reg_class_of_operand dest in
      let dest = assign_vreg dest_class dest in
      let* f = translate_operand f in
      let f_typ, f =
        match f with
        | Label (typ, l, []) -> (typ, l)
        | _ -> failwith "call: expected function to be label"
      in
      let float_args, int_args =
        List.partition (fun op -> reg_class_of_operand op = Float) args
      in
      let* int_args = translate_operands int_args in
      let* float_args = translate_operands float_args in
      let int_dests =
        List.(init (length int_args)) (call_conv ~caller:true state Target.Int)
      in
      let float_dests =
        List.(init (length float_args))
          (call_conv ~caller:true state Target.Float)
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
        instr "call" ~defs:[] ~uses:[ Label (f_typ, f, []) ]
        |> Target.modify_uses (fun ~uses ~num_hidden ->
            ( int_dests @ float_dests @ uses,
              num_hidden + List.length int_dests + List.length float_dests ))
        |> Target.modify_defs (fun ~defs ~num_hidden ->
            (clobbered @ defs, num_hidden + List.length clobbered))
      in
      let mov_instr =
        match dest_class with
        | Int -> Target.mov ~dest ~src:rax
        | Float -> Target.mov ~dest ~src:xmm0
      in
      let int_pcopies rest =
        if List.length int_dests > 0 then
          with_clobber_regs
            (Regs.caller_save
            |> List.map (fun r -> Physical r)
            |> RegSet.of_list)
            (pcopy ~dests:int_dests ~srcs:int_args)
          @> rest
        else rest
      in
      let float_pcopies rest =
        if List.length float_dests > 0 then
          with_clobber_regs
            (Regs.float_regs |> List.map (fun r -> Physical r) |> RegSet.of_list)
            (pcopy ~dests:float_dests ~srcs:float_args)
          @> rest
        else rest
      in
      int_pcopies @@ float_pcopies @@ call @> mov_instr @> k dest
    | Undag.Target.Goto (l, args) ->
      let* args = translate_operands args in
      Cfg.Last (Cfg.Branch (Target.goto l args, l))
    | Undag.Target.Cbranch (src1, src2, cond, l1, l1args, l2, l2args) ->
      let src1_class = reg_class_of_operand src1 in
      let src2_class = reg_class_of_operand src2 in
      let* src1 = translate_operand src1 in
      let* src2 = translate_operand src2 in
      let l1args_class = List.map reg_class_of_operand l1args in
      let* l1args = translate_operands l1args in
      let* l2args = translate_operands l2args in
      (* handle cbranches with the same label but different arguments *)
      if
        Cfg.equal_label l1 l2
        && not (List.equal Target.equal_operand l1args l2args)
      then
        let cmov arg1 _arg2 dest =
          match Target.(Option.map Reg.reg_class (destruct_reg dest)) with
          | Some Int ->
            Target.instr ~defs:[ dest ] ~uses:[ arg1 ]
              (match cond with
              | Graph.Cond.LT -> "cmovl"
              | LE -> "cmovle"
              | GT -> "cmovg"
              | GE -> "cmovge"
              | EQ -> "cmove"
              | NE -> "cmovne")
          | Some Float -> failwith "Float conditional moves not handled yet"
          | None -> failwith "Unknown register class for conditional move"
        in
        reuse_cond fresh_vreg src1_class src1 src2_class src2
          (fun () ->
            let open Target in
            let args =
              List.map
                (fun ((arg1_class, arg1), arg2) ->
                  let dest = Reg (fresh_vreg arg1_class) in
                  (arg1, arg2, dest))
                (List.combine (List.combine l1args_class l1args) l2args)
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
        @> instr "leaq" ~defs:[ dest ] ~uses:[ rsp_address ]
        @> k dest
      end
      else begin
        (* alloca in entry block, so use it as a stack slot *)
        let slot = state.new_stack_slot size in
        instr "leaq" ~defs:[ dest ] ~uses:[ slot ] @> k dest
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
      pcopy [(%33any, %32(%rdi))]
      jle label2, label3, %33any, $1
    label1(local=false)(96any):
      pcopy [(%97(%rax), %96any)]
      ret %97(%rax)
    label2(local=false)():
      movq %34any, %33any
      jmp label1(%34any)
    label3(local=false)():
      movq %37any, %33any
      subq %36(reuse=%37), %37any, $1
      pcopy [(%38(%rdi), %36(reuse=%37))]
      call %39(%rax), %40(%rcx), %41(%rdx), %42(%rsi), %43(%rdi), %44(%r8), %45(%r9), %46(%r10), %47(%r11), %48f(%xmm0), %49f(%xmm1), %50f(%xmm2), %51f(%xmm3), %52f(%xmm4), %53f(%xmm5), %54f(%xmm6), %55f(%xmm7), %56f(%xmm8), %57f(%xmm9), %58f(%xmm10), %59f(%xmm11), %60f(%xmm12), %61f(%xmm13), %62f(%xmm14), %63f(%xmm15), %38(%rdi), fibonacci
      movq %35any, %39(%rax)
      movq %66any, %33any
      subq %65(reuse=%66), %66any, $2
      pcopy [(%67(%rdi), %65(reuse=%66))]
      call %68(%rax), %69(%rcx), %70(%rdx), %71(%rsi), %72(%rdi), %73(%r8), %74(%r9), %75(%r10), %76(%r11), %77f(%xmm0), %78f(%xmm1), %79f(%xmm2), %80f(%xmm3), %81f(%xmm4), %82f(%xmm5), %83f(%xmm6), %84f(%xmm7), %85f(%xmm8), %86f(%xmm9), %87f(%xmm10), %88f(%xmm11), %89f(%xmm12), %90f(%xmm13), %91f(%xmm14), %92f(%xmm15), %67(%rdi), fibonacci
      movq %64any, %68(%rax)
      movq %95any, %35any
      addq %94(reuse=%95), %95any, %64any
      movq %93any, %94(reuse=%95)
      jmp label1(%93any)
    |}]

let%expect_test "Nested loops code generation" =
  let cfg = Examples.nested_loops in
  let _, cfg = codegen_test_helper (State.init ()) cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      movq %32any, $0
      jmp label6
    label1(local=false)():
      exit
    label2(local=false)(33any):
      jl label3, label1, %33any, $100
    label3(local=false)():
      movq %34any, %33any
      jmp label4(%33any, %34any)
    label4(local=false)(35any, 36any):
      jl label5, label2(%35any), %36any, $100
    label5(local=false)():
      movq %39any, %35any
      addq %38(reuse=%39), %39any, $1
      movq %37any, %38(reuse=%39)
      movq %42any, %36any
      addq %41(reuse=%42), %42any, $1
      movq %40any, %41(reuse=%42)
      jmp label4(%37any, %40any)
    label6(local=false)():
      jmp label2(%32any)
    |}]

let%expect_test "CBranch with both labels the same with different arguments" =
  let cfg = Examples.cbranch_same_label in
  let cfg = Undag.undag_graph cfg in
  let _, cfg = codegen_function ~args:[] (State.init ()) cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      movq %32any, $3
      movq %33any, $2
      movq %34any, $1
      movq %35any, $0
      jmp label1
    label1(local=false)():
      movq %36any, %35any
      movq %38any, %35any
      movq %39any, $2
      movq %40any, %32any
      cmp %37(reuse=%36), %36any, %34any
      cmove %38any, $1
      cmove %39any, %34any
      cmove %40any, %33any
      jmp label2(%38any, %39any, %40any)
    label2(local=false)(41any, 42any, 43any):
      exit
  |}]
