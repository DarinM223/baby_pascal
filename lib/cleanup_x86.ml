open X86

let cleanup (tmp : Target.physical_reg) (cfg : Cfg.graph) : Cfg.graph =
  let go_block _ block cfg =
    let head, tail = Cfg.unzip block in
    let ( @> ) i t = Cfg.Tail (Instruction i, t) in
    let rec go_tail = function
      | Cfg.Tail (Instruction i, tail) ->
        begin match i with
        (* lower moves with two memory operands *)
        | {
         Target.instr = "movq";
         defs = [ ((MemAddr _ | StackSlot _) as dest) ];
         uses = [ ((MemAddr _ | StackSlot _) as src) ];
        } ->
          Target.mov ~dest:(Reg (Physical tmp)) ~src
          @> Target.mov ~dest ~src:(Reg (Physical tmp))
          @> go_tail tail
        (* remove caller save definitions from calls *)
        | { Target.instr = "call"; _ } as instr ->
          { instr with Target.defs = [] } @> go_tail tail
        (* remove redundant moves *)
        | { Target.instr = "movq"; defs = [ dest ]; uses = [ src ] }
          when Target.(equal_operand (to_colored dest) (to_colored src)) ->
          go_tail tail
        (* todo: eliminate reuse operand uses *)
        | _ -> i @> go_tail tail
        end
      (* lower cmp instructions into cmp + j* *)
      | Cfg.Last
          (CBranch ({ instr; uses = _ :: _ :: first_use :: uses; _ }, l1, l2))
        when List.exists (fun (_, i) -> i = instr) Target.cond_mapping ->
        Target.mov ~dest:(Reg (Physical tmp)) ~src:first_use
        @> Target.instr "cmp" ~defs:[ Reg (Physical tmp) ] ~uses
        @> Target.instr instr ~defs:[] ~uses:[ Label (l1, []) ]
        @> Cfg.Last (Branch (Target.goto l2 [], l2))
      | Cfg.Last l -> Cfg.Last l
    in
    let tail = go_tail tail in
    Cfg.Blocks.insert (Cfg.zip (head, tail)) cfg
  in
  Cfg.Blocks.fold go_block cfg Cfg.empty
