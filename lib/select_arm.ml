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
    | Undag.Target.Reg n ->
      let vreg = fresh_vreg clz in
      NameHashtbl.add mapping n (Reg vreg);
      vreg
    | _ -> failwith "assign_vreg: expected destination to be register"
end

module Select = struct
  module Graph = Arm.Cfg
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

  let rec select ({ State.fresh_vreg; mapping; _ } as state)
      (instruction : Undag.Target.instr) (k : Target.operand -> Cfg.tail) :
      Cfg.tail =
    let assign_vreg clz reg = Target.Reg (State.assign_vreg state clz reg) in
    let reuse_instr tmp dest instr =
      instr
      |> Target.modify_uses (fun ~uses ~num_hidden ->
          (tmp :: uses, num_hidden + 1))
      |> Target.modify_defs (fun ~defs ~num_hidden ->
          (Target.reuse_op tmp dest :: defs, num_hidden))
    in
    let rec translate_operand :
        Undag.Target.operand -> (Target.operand -> 'a) -> 'a = function
      | Undag.Target.Instr src -> select state src
      | Undag.Target.Const i -> fun k -> k (Target.Imm i)
      | Undag.Target.Reg r ->
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
    let ( @> ) i t = Cfg.Tail (Instruction i, t) in
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
      let reuse_cond code =
        let tmp1 = Reg (fresh_vreg Int) in
        let tmp2 = Reg (fresh_vreg Int) in
        mov ~dest:tmp1 ~src:src1
        @> reuse_instr tmp1 tmp2 (instr "cmp" ~defs:[] ~uses:[ src2 ])
        @> reuse_instr tmp2 dest
             (instr "cset" ~defs:[] ~uses:[ ConditionCode code ])
        @> k dest
      in
      begin match bop with
      | Ast.Add -> mk_bop "add"
      | Ast.Sub -> mk_bop "sub"
      | Ast.Mul -> mk_bop "mul"
      | Ast.Div -> mk_bop "sdiv" (* signed because we used idiv in X86 *)
      | Ast.Eq -> reuse_cond Eq
      | Ast.Neq -> reuse_cond Ne
      | Ast.Lt -> reuse_cond Lt
      | Ast.Le -> reuse_cond Le
      | Ast.Gt -> reuse_cond Gt
      | Ast.Ge -> reuse_cond Ge
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
    | Undag.Target.Call _ -> failwith "todo"
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
    | Undag.Target.Alloca _ -> failwith "todo"
    | Undag.Target.Load _ -> failwith "todo"
    | Undag.Target.Store _ -> failwith "todo"
end
