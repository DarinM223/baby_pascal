open X86

module IntSet = Utils.IntSet
module RegSet = Set.Make (X86.Target.Reg)
module RegHashtbl = CCHashtbl.Make (X86.Target.Reg)

(** aligns stack offset to multiple of 16 if a function is called *)
let align_stack_offset called_function offset =
  (* (n + 15) & ~15 to round up to the next multiple of 16,
     the stack is already misaligned by 8,
     returns the new offset (still not counting the 8 bytes pushed at the start) *)
  if called_function then begin
    let offset' = ((offset + 8 + 15) land lnot 15) - 8 in
    Logs.debug (fun m ->
        m "aligning stack initial offset: %d final offset: %d\n" offset offset');
    offset'
  end
  else offset

let cleanup (state : Select_x86.State.t) (tmp_int : Target.physical_reg)
    (tmp_float : Target.physical_reg) (cfg : Cfg.graph) : Cfg.graph =
  let callee_save =
    RegSet.of_list (List.map (fun p -> Target.Physical p) Regs.callee_save)
  in
  let used_callee_saves = RegHashtbl.create (List.length Regs.callee_save) in
  let called_function = ref false in
  let record_reg reg =
    if RegSet.mem reg callee_save && not (RegHashtbl.mem used_callee_saves reg)
    then RegHashtbl.add used_callee_saves reg (state.new_stack_slot 8)
  in
  let rec record_operand op =
    match X86.Target.to_colored op with
    | Reg reg -> if not (X86.Target.Reg.is_tombstone reg) then record_reg reg
    | MemAddr { base; index; _ } ->
      Option.iter record_reg base;
      record_reg index
    | Label (_, _, args) -> List.iter record_operand args
    | _ -> ()
  in
  let restore tail =
    let aligned_stack_offset =
      align_stack_offset !called_function state.stack_offset
    in
    let tail =
      match state.frame_pointer with
      | Some fp ->
        Cfg.Tail
          ( Instruction
              (Target.mov ~dest:(Reg (Physical Regs.rsp)) ~src:(Reg fp)),
            Cfg.Tail
              (Instruction (Target.instr "popq" ~defs:[] ~uses:[ Reg fp ]), tail)
          )
      | None ->
        if aligned_stack_offset > 0 then
          Cfg.Tail
            ( Instruction
                (Target.instr "addq"
                   ~defs:[ Reg (Physical Regs.rsp) ]
                   ~uses:[ Imm aligned_stack_offset ]),
              tail )
        else tail
    in
    RegHashtbl.fold
      (fun reg slot tail ->
        Cfg.Tail (Cfg.Instruction (Target.mov ~dest:(Reg reg) ~src:slot), tail))
      used_callee_saves tail
  in
  let prelude head =
    let aligned_stack_offset =
      align_stack_offset !called_function state.stack_offset
    in
    let head =
      match state.frame_pointer with
      | Some fp ->
        Cfg.Head
          ( Cfg.Head
              ( head,
                Instruction (Target.instr "pushq" ~defs:[] ~uses:[ Reg fp ]) ),
            Instruction
              (Target.mov ~dest:(Reg fp) ~src:(Reg (Physical Regs.rsp))) )
      | None -> head
    in
    let head =
      if aligned_stack_offset > 0 then
        Cfg.Head
          ( head,
            Instruction
              (Target.instr "subq"
                 ~defs:[ Reg (Physical Regs.rsp) ]
                 ~uses:[ Imm aligned_stack_offset ]) )
      else head
    in
    RegHashtbl.fold
      (fun reg slot head ->
        Cfg.Head (head, Cfg.Instruction (Target.mov ~dest:slot ~src:(Reg reg))))
      used_callee_saves head
  in
  let lower_immediate_jump f = function
    | (X86.Target.Imm _ as src), reg ->
      Logs.debug (fun m ->
          m "Post regalloc adding move for immediate jump arg: %a <- %a\n"
            X86.Target.pp_reg reg X86.Target.pp_operand src);
      fun tail ->
        X86.Cfg.Tail
          (Instruction (X86.Target.mov ~dest:(X86.Target.Reg reg) ~src), f tail)
    | _ -> f
  in
  (* convert jump arguments that are immediates to moves *)
  let lower_jump_label ls f = function
    | X86.Target.Label (clz, l', args)
      when List.exists (fun l -> X86.Target.equal_label l' l) ls ->
      let phis =
        match X86.Cfg.(firstt (fst (fst (focus (idd (Some l')) cfg)))) with
        | Entry -> []
        | Label (_, info) -> info.args
      in
      let tail =
        List.fold_left lower_immediate_jump f (Utils.combine_drop args phis)
      in
      (tail, X86.Target.Label (clz, l', args))
    | op -> (f, op)
  in
  let go_block cfg block =
    let head, tail = Cfg.unzip block in
    let ( @> ) i t = Cfg.Tail (Instruction i, t) in
    let rec go_tail = function
      | Cfg.Tail (Instruction i, tail) ->
        begin match i with
        (* lower conditional moves with immediate source operand *)
        | {
         Target.instr =
           "cmove" | "cmovne" | "cmovge" | "cmovg" | "cmovle" | "cmovl";
         uses = [ (Imm _ as src) ];
         _;
        } ->
          Target.mov ~dest:(Reg (Physical tmp_int)) ~src
          @> { i with uses = [ Reg (Physical tmp_int) ] }
          @> go_tail tail
        (* lower moves with two memory operands *)
        | {
         Target.instr = "movq";
         defs = [ ((MemAddr _ | StackSlot _ | Label _) as dest) ];
         uses = [ ((MemAddr _ | StackSlot _ | Label _) as src) ];
         _;
        } ->
          Target.mov ~dest:(Reg (Physical tmp_int)) ~src
          @> Target.mov ~dest ~src:(Reg (Physical tmp_int))
          @> go_tail tail
        | {
         Target.instr = "movsd";
         defs = [ ((MemAddr _ | StackSlot _ | Label _) as dest) ];
         uses = [ ((MemAddr _ | StackSlot _ | Label _) as src) ];
         _;
        } ->
          Target.mov ~dest:(Reg (Physical tmp_float)) ~src
          @> Target.mov ~dest ~src:(Reg (Physical tmp_float))
          @> go_tail tail
        (* remove redundant moves *)
        | { Target.instr = "movq"; defs = [ dest ]; uses = [ src ]; _ }
          when Target.(equal_operand (to_colored dest) (to_colored src)) ->
          go_tail tail
        | _ ->
          if i.instr = "call" then called_function := true;
          List.iter record_operand i.uses;
          List.iter record_operand i.defs;
          i @> go_tail tail
        end
        (* lower cmp instructions into cmp + j* *)
      | Cfg.Last
          (CBranch
             ( ({
                  instr;
                  uses = Label (Float, _, _) :: _ :: first_use :: uses;
                  defs;
                  _;
                } as i),
               l1,
               l2 ))
        when List.exists (fun (_, i) -> i = instr) Target.float_cond_mapping ->
        List.iter record_operand (first_use :: uses);
        List.iter record_operand defs;
        let tail, _ =
          X86.Target.fold_uses (lower_jump_label [ l1; l2 ]) Fun.id i
        in
        tail
        @@ Target.mov ~dest:(Reg (Physical tmp_float)) ~src:first_use
        @> Target.instr "ucomisd" ~defs:[ Reg (Physical tmp_float) ] ~uses
        @> Target.instr instr ~defs:[] ~uses:[ Label (Float, l1, []) ]
        @> Cfg.Last (Branch (Target.goto l2 [], l2))
      | Cfg.Last
          (CBranch
             ( ({ instr; uses = _ :: _ :: first_use :: uses; defs; _ } as i),
               l1,
               l2 ))
        when List.exists (fun (_, i) -> i = instr) Target.int_cond_mapping ->
        List.iter record_operand (first_use :: uses);
        List.iter record_operand defs;
        let tail, _ =
          X86.Target.fold_uses (lower_jump_label [ l1; l2 ]) Fun.id i
        in
        tail
        @@ Target.mov ~dest:(Reg (Physical tmp_int)) ~src:first_use
        @> Target.instr "cmp" ~defs:[ Reg (Physical tmp_int) ] ~uses
        @> Target.instr instr ~defs:[] ~uses:[ Label (Int, l1, []) ]
        @> Cfg.Last (Branch (Target.goto l2 [], l2))
      | Cfg.Last (CBranch _) as tail ->
        failwith
        @@ Format.asprintf "cleanup_x86: invalid conditional branch: %a"
             X86.Cfg.pp_tail tail
      | Cfg.Last (Branch (i, l)) ->
        List.iter record_operand i.uses;
        List.iter record_operand i.defs;
        let tail, i = X86.Target.fold_uses (lower_jump_label [ l ]) Fun.id i in
        tail (Cfg.Last (Branch (i, l)))
      | Cfg.Last (Return i) ->
        List.iter record_operand i.uses;
        List.iter record_operand i.defs;
        restore (Cfg.Last (Return i))
      | Cfg.Last Exit -> restore (Cfg.Last Exit)
    in
    let tail = go_tail tail in
    Cfg.Blocks.insert (Cfg.zip (head, tail)) cfg
  in
  let rpo = Cfg.reverse_postorder_dfs cfg in
  let cfg = List.fold_left go_block Cfg.empty rpo in
  let (head, tail), rest = Cfg.focus_entry cfg in
  Cfg.unfocus ((prelude head, tail), rest)
