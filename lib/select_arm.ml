open Arm
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
  module G = Arm.Cfg
  module State = State

  let reg_class_of_operand _ = Target.Int

  let call_conv ~caller { State.fresh_vreg; new_stack_slot; _ } = function
    | Target.Int ->
      begin function
        | 0 -> Target.(Reg (constrained Regs.x0 (fresh_vreg Int)))
        | 1 -> Target.(Reg (constrained Regs.x1 (fresh_vreg Int)))
        | 2 -> Target.(Reg (constrained Regs.x2 (fresh_vreg Int)))
        | 3 -> Target.(Reg (constrained Regs.x3 (fresh_vreg Int)))
        | 4 -> Target.(Reg (constrained Regs.x4 (fresh_vreg Int)))
        | 5 -> Target.(Reg (constrained Regs.x5 (fresh_vreg Int)))
        | 6 -> Target.(Reg (constrained Regs.x6 (fresh_vreg Int)))
        | 7 -> Target.(Reg (constrained Regs.x7 (fresh_vreg Int)))
        | n ->
          if caller then new_stack_slot 8
          else
            Target.StackSlot { relative_to_base = true; offset = (n - 7) * 8 }
      end
    | Target.Float -> failwith "Float calling convention not supported yet"

  let reuse_instr tmp dest instr =
    instr
    |> Target.modify_uses (fun ~uses ~num_hidden ->
        (tmp :: uses, num_hidden + 1))
    |> Target.modify_defs (fun ~defs ~num_hidden ->
        (Target.reuse_op tmp dest :: defs, num_hidden))
  let ( @> ) i t = Cfg.Tail (Instruction i, t)

  let reuse_cond fresh src1 src2 init k mk_instr =
    let open Target in
    let tmp1 = Reg (fresh (reg_class_of_operand src1)) in
    let tmp2 = Reg (fresh (reg_class_of_operand src1)) in
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
            let pp_sep fmt () = Format.pp_print_string fmt "," in
            failwith
            @@ Format.asprintf
                 "Select_Arm: Register %a not found in mapping %a\n"
                 Normalize.Name.pp r
                 (NameHashtbl.pp ~pp_sep Normalize.Name.pp Target.pp_operand)
                 mapping
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
      let dest = assign_vreg Int dest in
      let* src = translate_operand src in
      mov ~dest ~src @> k dest
    (* todo: could be done if we could statically check if a Not is for an integer or boolean *)
    (* | Undag.Target.Uop (dest, Not, src) ->
      let open Target in
      let dest = assign_vreg Int dest in
      let* src = translate_operand src in
      instr "eor" ~defs:[ reuse_op src dest ] ~uses:[ src; Imm 1 ] @> k dest *)
    | Undag.Target.Uop (dest, Not, src) ->
      let open Target in
      let dest = assign_vreg Int dest in
      let tmp = Reg (fresh_vreg Int) in
      let* src = translate_operand src in
      reuse_instr src tmp (instr "cmp" ~defs:[] ~uses:[ Imm 0 ])
      @> reuse_instr tmp dest (instr "cset" ~defs:[] ~uses:[ ConditionCode Eq ])
      @> k dest
    | Undag.Target.Bop (dest, bop, src1, src2) ->
      let open Target in
      let dest = assign_vreg Int dest in
      let* src1 = translate_operand src1 in
      let* src2 = translate_operand src2 in
      let mk_bop i = instr i ~defs:[ dest ] ~uses:[ src1; src2 ] @> k dest in
      let instr_of_cond code _arg tmp dest =
        reuse_instr tmp dest
          (instr "cset" ~defs:[] ~uses:[ ConditionCode code ])
      in
      let reuse_cond =
        reuse_cond fresh_vreg src1 src2
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
      begin match bop with
      | Ast.Add -> mk_bop "add"
      | Ast.Sub -> mk_bop "sub"
      | Ast.Mul -> mk_bop "mul"
      | Ast.Div -> mk_bop "sdiv" (* signed because we used idiv in X86 *)
      | Ast.Eq -> reuse_cond (instr_of_cond Eq)
      | Ast.Neq -> reuse_cond (instr_of_cond Ne)
      | Ast.Lt -> reuse_cond (instr_of_cond Lt)
      | Ast.Le -> reuse_cond (instr_of_cond Le)
      | Ast.Gt -> reuse_cond (instr_of_cond Gt)
      | Ast.Ge -> reuse_cond (instr_of_cond Ge)
      | Ast.And -> mk_bop "and"
      | Ast.Or -> mk_bop "orr"
      end
    | Undag.Target.Return ops ->
      let* ops = translate_operands ops in
      begin match ops with
      | [] -> Cfg.Last (Cfg.Return (Target.return ~uses:[]))
      | [ op ] ->
        let x0 = Target.(Reg (constrained Regs.x0 (fresh_vreg Int))) in
        Target.pcopy ~dests:[ x0 ] ~srcs:[ op ]
        @> Cfg.Last (Cfg.Return (Target.return ~uses:[ x0 ]))
      | [ op1; op2 ] ->
        let x0 = Target.(Reg (constrained Regs.x0 (fresh_vreg Int))) in
        let x1 = Target.(Reg (constrained Regs.x1 (fresh_vreg Int))) in
        Target.pcopy ~dests:[ x0; x1 ] ~srcs:[ op1; op2 ]
        @> Cfg.Last (Cfg.Return (Target.return ~uses:[ x0; x1 ]))
      | _ -> failwith "can only return two things currently"
      end
    | Undag.Target.Call (dest, f, args) ->
      let open Target in
      let dest = assign_vreg (reg_class_of_operand dest) dest in
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
        List.map
          (fun r -> Reg (constrained r (fresh_vreg Int)))
          Regs.caller_save
      in
      let x0 =
        List.find
          (function
            | Reg (Virtual { reg_constr = UsePhysical r; _ }) when r = Regs.x0
              ->
              true
            | _ -> false)
          clobbered
      in
      let call =
        instr "bl" ~defs:[] ~uses:[ Label (f, []) ]
        |> Target.modify_uses (fun ~uses ~num_hidden ->
            (dests @ uses, num_hidden + List.length dests))
        |> Target.modify_defs (fun ~defs ~num_hidden ->
            (clobbered @ defs, num_hidden + List.length clobbered))
      in
      with_clobber_regs
        (Regs.caller_save |> List.map (fun r -> Physical r) |> RegSet.of_list)
        (pcopy ~dests ~srcs:args)
      @> call @> mov ~dest ~src:x0 @> k dest
    | Undag.Target.Goto (l, args) ->
      let* args = translate_operands args in
      Cfg.Last (Cfg.Branch (Target.goto l args, l))
    | Undag.Target.Cbranch (src1, src2, cond, l1, l1args, l2, l2args) ->
      let* src1 = translate_operand src1 in
      let* src2 = translate_operand src2 in
      let* l1args = translate_operands l1args in
      let* l2args = translate_operands l2args in
      (* handle cbranches with the same label but different arguments *)
      if
        Cfg.equal_label l1 l2
        && not (List.equal Target.equal_operand l1args l2args)
      then
        let code =
          match cond with
          | Graph.Cond.LT -> Target.Lt
          | LE -> Le
          | GT -> Gt
          | GE -> Ge
          | EQ -> Eq
          | NE -> Ne
        in
        let instr_of_cond code arg tmp dest =
          Target.instr "csel" ~defs:[ dest ]
            ~uses:[ arg; tmp; Target.ConditionCode code ]
        in
        reuse_cond fresh_vreg src1 src2
          (fun () ->
            let open Target in
            let args =
              List.map
                (fun (arg1, arg2) ->
                  let dest = Reg (fresh_vreg Int) in
                  (arg1, arg2, dest))
                (List.combine l1args l2args)
            in
            (args, fun t -> t))
          (fun dests -> Cfg.Last (Cfg.Branch (Target.goto l1 dests, l1)))
          (instr_of_cond code)
      else
        Cfg.Last
          (Cfg.CBranch
             ( Target.cbranch ~args:[ src1; src2 ] cond l1 l1args l2 l2args,
               l1,
               l2 ))
    | Undag.Target.Alloca (dest, size) ->
      let open Target in
      let dest = assign_vreg Int dest in
      if state.curr_block <> X86.Cfg.entry_uid then begin
        state.frame_pointer <- Some (Physical Regs.x29);
        (* for dynamic allocas, you need to manually increase the stack *)
        instr "sub" ~defs:[ Reg (Physical Regs.sp) ]
          ~uses:[ Reg (Physical Regs.sp); Imm size ]
        @> mov ~dest ~src:(Reg (Physical Regs.sp))
        @> k dest
      end
      else
        (* alloca in entry block, so use it as a stack slot *)
        begin match (state.new_stack_slot size, state.frame_pointer) with
        | Target.StackSlot { relative_to_base = true; offset; _ }, Some fp ->
          (if offset = 0 then Target.mov ~dest ~src:(Reg fp)
           else Target.instr "add" ~defs:[ dest ] ~uses:[ Reg fp; Imm offset ])
          @> k dest
        | Target.StackSlot { relative_to_base = false; offset; _ }, _ ->
          (if offset = 0 then Target.mov ~dest ~src:(Reg (Physical Regs.sp))
           else
             Target.instr "add" ~defs:[ dest ]
               ~uses:[ Reg (Physical Regs.sp); Imm offset ])
          @> k dest
        | _ -> failwith "Expected stack slot for alloca"
        end
    | Undag.Target.Load (dest, src) ->
      let dest = assign_vreg (reg_class_of_operand dest) dest in
      let* src = translate_operand src in
      begin match src with
      | Reg reg ->
        let src =
          Target.MemAddr
            {
              base = reg;
              displacement = 0;
              scale = 0;
              index = reg;
              preindexed = false;
            }
        in
        Target.mov ~dest ~src @> k dest
      | _ -> failwith "Select_Arm: expected source of load to be a register"
      end
    | Undag.Target.Store (dest, value) ->
      let* dest = translate_operand dest in
      let* value = translate_operand value in
      begin match dest with
      | Reg reg ->
        let dest =
          Target.MemAddr
            {
              base = reg;
              displacement = 0;
              scale = 0;
              index = reg;
              preindexed = false;
            }
        in
        Target.mov ~dest ~src:value @> k (Imm 0)
      | _ ->
        failwith "Select_Arm: expected destination of store to be a register"
      end
end

include Isa.Codegen (Target) (Arm.Cfg) (Select)

let%expect_test "Fibonacci code generation" =
  let cfg = Examples.fibonacci in
  let _, cfg =
    codegen_test_helper ~args:[ (TInteger, "v") ] (State.init ()) cfg
  in
  Format.printf "%a" Arm.Printer.pp_graph cfg;
  [%expect
    {|
      pcopy [(1any, 0(%x0))]
      ble label2, label3, 1any, #1
    label1(local=false)(51any):
      pcopy [(52(%x0), 51any)]
      ret 52(%x0)
    label2(local=false)():
      mov 2any, 1any
      b label1(2any)
    label3(local=false)():
      sub 4any, 1any, #1
      pcopy [(5(%x0), 4any)]
      bl 6(%x0), 7(%x1), 8(%x2), 9(%x3), 10(%x4), 11(%x5), 12(%x6), 13(%x7), 14(%x8), 15(%x9), 16(%x10), 17(%x11), 18(%x12), 19(%x13), 20(%x14), 21(%x15), 22(%x16), 23(%x17), 24(%x18), 25(%x30), 5(%x0), fibonacci
      mov 3any, 6(%x0)
      sub 27any, 1any, #2
      pcopy [(28(%x0), 27any)]
      bl 29(%x0), 30(%x1), 31(%x2), 32(%x3), 33(%x4), 34(%x5), 35(%x6), 36(%x7), 37(%x8), 38(%x9), 39(%x10), 40(%x11), 41(%x12), 42(%x13), 43(%x14), 44(%x15), 45(%x16), 46(%x17), 47(%x18), 48(%x30), 28(%x0), fibonacci
      mov 26any, 29(%x0)
      add 50any, 3any, 26any
      mov 49any, 50any
      b label1(49any)
    |}]

let%expect_test "Nested loops code generation" =
  let cfg = Examples.nested_loops in
  let _, cfg = codegen_test_helper (State.init ()) cfg in
  Format.printf "%a" Arm.Printer.pp_graph cfg;
  [%expect
    {|
      mov 0any, #0
      b label6
    label1(local=false)():
      exit
    label2(local=false)(1any):
      blt label3, label1, 1any, #100
    label3(local=false)():
      mov 2any, 1any
      b label4(1any, 2any)
    label4(local=false)(3any, 4any):
      blt label5, label2(3any), 4any, #100
    label5(local=false)():
      add 6any, 3any, #1
      mov 5any, 6any
      add 8any, 4any, #1
      mov 7any, 8any
      b label4(5any, 7any)
    label6(local=false)():
      b label2(0any)
    |}]

let%expect_test "CBranch with both labels the same with different arguments" =
  let cfg = Examples.cbranch_same_label in
  let cfg =
    Normalize.Cfg.Blocks.fold
      (fun _ block acc -> Undag.Cfg.Blocks.insert (Undag.undag block) acc)
      cfg Undag.Cfg.empty
  in
  let _, cfg = codegen_function ~args:[] (State.init ()) cfg in
  Format.printf "%a" Arm.Printer.pp_graph cfg;
  [%expect
    {|
      mov 0any, #3
      mov 1any, #2
      mov 2any, #1
      mov 3any, #0
      b label1
    label1(local=false)():
      mov 4any, 3any
      cmp 5(reuse=%4), 4any, 2any
      csel 6any, #1, 3any, eq
      csel 7any, 2any, #2, eq
      csel 8any, 1any, 0any, eq
      b label2(6any, 7any, 8any)
    label2(local=false)(9any, 10any, 11any):
      exit
    |}]
