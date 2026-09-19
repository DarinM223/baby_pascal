open Arm

module IntSet = Utils.IntSet
module RegSet = Set.Make (Arm.Target.Reg)
module RegHashtbl = CCHashtbl.Make (Arm.Target.Reg)

(** aligns stack offset to multiple of 16 if a function is called *)
let align_stack_offset called_function offset =
  if called_function && offset mod 16 <> 0 then offset + 8 else offset

let ( @> ) i t = Cfg.Tail (Instruction i, t)
let rec append_tail head = function
  | Cfg.Tail (i, tail) -> append_tail (Cfg.Head (head, i)) tail
  | Cfg.Last _ -> head

let cleanup (state : Select_arm.State.t) (tmp1 : Target.physical_reg)
    (tmp2 : Target.physical_reg) (cfg : Cfg.graph) : Cfg.graph =
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
    match Arm.Target.to_colored op with
    | Reg reg -> if not (Arm.Target.Reg.is_tombstone reg) then record_reg reg
    | MemAddr { base; index; _ } ->
      record_reg base;
      record_reg index
    | Label (_, args) -> List.iter record_operand args
    | _ -> ()
  in
  (* loads and stores can't have sp as an operand so use temporaries in that case *)
  let store ~dest ~src =
    match src with
    | Target.Reg (Physical phys) when Target.equal_physical_reg phys Arm.Regs.sp
      ->
      fun t ->
        Target.mov ~dest:(Reg (Physical tmp1)) ~src
        @> Target.instr "str" ~defs:[] ~uses:[ Reg (Physical tmp1); dest ]
        @> t
    | _ -> fun t -> Target.instr "str" ~defs:[] ~uses:[ src; dest ] @> t
  in
  let load ~dest ~src =
    match dest with
    | Target.Reg (Physical phys) when Target.equal_physical_reg phys Arm.Regs.sp
      ->
      fun t ->
        Target.instr "ldr" ~defs:[ Reg (Physical tmp1) ] ~uses:[ src ]
        @> Target.mov ~dest ~src:(Reg (Physical tmp1))
        @> t
    | _ -> fun t -> Target.instr "ldr" ~defs:[ dest ] ~uses:[ src ] @> t
  in
  let restore tail =
    let aligned_stack_offset =
      align_stack_offset !called_function state.stack_offset
    in
    let tail =
      Cfg.Tail
        ( Instruction
            (Target.instr "ldp"
               ~defs:[ Reg (Physical Regs.x29); Reg (Physical Regs.x30) ]
               ~uses:
                 [
                   MemAddr
                     {
                       base = Physical Regs.sp;
                       index = Physical Regs.sp;
                       scale = 0;
                       displacement = 0;
                       preindexed = false;
                     };
                   Imm 16;
                 ]),
          tail )
    in
    let tail =
      match state.frame_pointer with
      | Some fp ->
        Cfg.Tail
          ( Instruction (Target.mov ~dest:(Reg (Physical Regs.sp)) ~src:(Reg fp)),
            tail )
      | None ->
        if aligned_stack_offset > 0 then
          Cfg.Tail
            ( Instruction
                (Target.instr "add" ~defs:[ Reg (Physical Regs.sp) ]
                   ~uses:[ Reg (Physical Regs.sp); Imm aligned_stack_offset ]),
              tail )
        else tail
    in
    RegHashtbl.fold
      (fun reg slot -> load ~dest:(Reg reg) ~src:slot)
      used_callee_saves tail
  in
  let prelude head =
    let aligned_stack_offset =
      align_stack_offset !called_function state.stack_offset
    in
    let head =
      Cfg.Head
        ( head,
          Instruction
            (Target.instr "stp" ~defs:[]
               ~uses:
                 [
                   Reg (Physical Regs.x29);
                   Reg (Physical Regs.x30);
                   MemAddr
                     {
                       base = Target.Physical Regs.sp;
                       index = Target.Physical Regs.sp;
                       scale = 0;
                       displacement = -16;
                       preindexed = true;
                     };
                 ]) )
    in
    let head =
      match state.frame_pointer with
      | Some fp ->
        Cfg.Head
          ( head,
            Instruction
              (Target.mov ~dest:(Reg fp) ~src:(Reg (Physical Regs.sp))) )
      | None -> head
    in
    let head =
      if aligned_stack_offset > 0 then
        Cfg.Head
          ( head,
            Instruction
              (Target.instr "sub" ~defs:[ Reg (Physical Regs.sp) ]
                 ~uses:[ Reg (Physical Regs.sp); Imm aligned_stack_offset ]) )
      else head
    in
    RegHashtbl.fold
      (fun reg slot head ->
        append_tail head (store ~dest:slot ~src:(Reg reg) (Cfg.Last Cfg.Exit)))
      used_callee_saves head
  in
  let lower_immediate_jump f = function
    | (Arm.Target.Imm _ as src), reg ->
      Logs.debug (fun m ->
          m "Post regalloc adding move for immediate jump arg: %a <- %a\n"
            Arm.Target.pp_reg reg Arm.Target.pp_operand src);
      fun tail ->
        Arm.Cfg.Tail
          (Instruction (Arm.Target.mov ~dest:(Arm.Target.Reg reg) ~src), f tail)
    | _ -> f
  in
  (* convert jump arguments that are immediates to moves *)
  let lower_jump_label f = function
    | Arm.Target.Label (l', args) ->
      let phis =
        match Arm.Cfg.(firstt (fst (fst (focus (idd (Some l')) cfg)))) with
        | Entry -> []
        | Label (_, info) -> info.args
      in
      let tail =
        List.fold_left lower_immediate_jump f (List.combine args phis)
      in
      (tail, Arm.Target.Label (l', args))
    | op -> (f, op)
  in
  let go_block cfg block =
    let head, tail = Cfg.unzip block in
    let move_immediates_to_temps src1 src2 ~modify ~no_imms =
      begin match (src1, src2) with
      | (Target.Imm _ as src1), (Target.Imm _ as src2) ->
        Target.mov ~dest:(Reg (Physical tmp1)) ~src:src1
        @> Target.mov ~dest:(Reg (Physical tmp2)) ~src:src2
        @> modify (Target.Reg (Physical tmp1)) (Target.Reg (Physical tmp2))
      | (Imm _ as src1), src2 ->
        Target.mov ~dest:(Reg (Physical tmp1)) ~src:src1
        @> modify (Target.Reg (Physical tmp1)) src2
      | src1, (Imm _ as src2) ->
        Target.mov ~dest:(Reg (Physical tmp1)) ~src:src2
        @> modify src1 (Target.Reg (Physical tmp1))
      | _ -> no_imms src1 src2
      end
    in
    let rec go_tail = function
      | Cfg.Tail (Instruction i, tail) ->
        begin match i with
        (* lower conditional moves with immediate source operand *)
        | {
         Target.instr = "csel";
         uses =
           (Imm _ as src1) :: src2 :: rest | src1 :: (Imm _ as src2) :: rest;
         _;
        } ->
          move_immediates_to_temps src1 src2
            ~modify:(fun src1 src2 ->
              { i with uses = src1 :: src2 :: rest } @> go_tail tail)
            ~no_imms:(fun _ _ ->
              failwith "cleanup_arm: this shouldn't with csel")
        (* lower mul and sdiv with immediate operands *)
        | {
         Target.instr = "mul" | "sdiv";
         defs = _;
         uses = src1 :: src2 :: rest;
         _;
        } ->
          move_immediates_to_temps src1 src2
            ~modify:(fun src1 src2 ->
              { i with uses = src1 :: src2 :: rest } @> go_tail tail)
            ~no_imms:(fun _ _ -> i @> go_tail tail)
        (* lower moves with two memory operands *)
        | {
         Target.instr = "mov";
         defs = [ ((MemAddr _ | StackSlot _) as dest) ];
         uses = [ ((MemAddr _ | StackSlot _) as src) ];
         _;
        } ->
          Target.mov ~dest:(Reg (Physical tmp1)) ~src
          @> Target.mov ~dest ~src:(Reg (Physical tmp1))
          @> go_tail tail
        (* lower move with destination memory operand into store *)
        | {
         Target.instr = "mov";
         defs = [ ((MemAddr _ | StackSlot _) as dest) ];
         uses = [ src ];
         _;
        } ->
          store ~dest ~src (go_tail tail)
        (* lower move with source memory operand into load *)
        | {
         Target.instr = "mov";
         defs = [ dest ];
         uses = [ ((MemAddr _ | StackSlot _) as src) ];
         _;
        } ->
          load ~dest ~src (go_tail tail)
        (* remove redundant moves *)
        | { Target.instr = "mov"; defs = [ dest ]; uses = [ src ]; _ }
          when Target.(equal_operand (to_colored dest) (to_colored src)) ->
          go_tail tail
        | _ ->
          List.iter record_operand i.uses;
          List.iter record_operand i.defs;
          i @> go_tail tail
        end
      (* lower cmp instructions into cmp + j* *)
      | Cfg.Last
          (CBranch
             ( ({ instr; uses = _ :: _ :: first_use :: uses; defs; _ } as i),
               l1,
               l2 ))
        when List.exists (fun (_, i) -> i = instr) Target.cond_mapping ->
        List.iter record_operand (first_use :: uses);
        List.iter record_operand defs;
        let tail, _ = Arm.Target.fold_uses lower_jump_label Fun.id i in
        tail
        @@ Target.mov ~dest:(Reg (Physical tmp1)) ~src:first_use
        @> Target.instr "cmp" ~defs:[ Reg (Physical tmp1) ] ~uses
        @> Target.instr instr ~defs:[] ~uses:[ Label (l1, []) ]
        @> Cfg.Last (Branch (Target.goto l2 [], l2))
      | Cfg.Last (CBranch _) ->
        failwith "cleanup_arm: invalid conditional branch"
      | Cfg.Last (Branch (i, l)) ->
        List.iter record_operand i.uses;
        List.iter record_operand i.defs;
        let tail, i = Arm.Target.fold_uses lower_jump_label Fun.id i in
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
