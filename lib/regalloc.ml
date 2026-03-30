type state = {
  processed : bool array;
  liveness : Spill.Liveness.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
}

let get_register _state _var _occupied = failwith ""

let enforce_constraints _state _instr = ()

let implement_phi_copies _state ~src:_ ~dest:_ = ()

let dies state uid a instr_num =
  match state.liveness.dies uid a with
  | Some num when num <= instr_num -> true
  | _ -> false

let color_block state ((first, tail) as block : X86.Cfg.block) : unit =
  let uid = X86.Cfg.id block in
  let occupied = ref (state.liveness.live_in uid) in
  let phis =
    match first with
    | X86.Cfg.Entry -> []
    | X86.Cfg.Label (_, info) -> info.args
  in
  List.iter
    (function
      | X86.Target.Virtual phi' as phi ->
        phi'.reg <- get_register state phi !occupied;
        occupied := X86.Target.RegSet.add phi'.reg !occupied
      | _ -> ())
    phis;
  let handle_instruction instr_num instr =
    enforce_constraints state instr;
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual a' as a when dies state uid a instr_num ->
          occupied := X86.Target.(RegSet.remove a'.reg !occupied)
        | _ -> ())
      (X86.Target.uses instr);
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual r' as r ->
          r'.reg <- get_register state r !occupied;
          occupied := X86.Target.RegSet.add r'.reg !occupied
        | _ -> ())
      (X86.Target.defs instr)
  in
  let rec go instr_num = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      handle_instruction instr_num instr;
      go (instr_num + 1) tail
    | X86.Cfg.Last l ->
      begin match l with
      | X86.Printer.Exit -> ()
      | X86.Printer.Branch (i, _) -> handle_instruction instr_num i
      | X86.Printer.CBranch (i, _, _) -> handle_instruction instr_num i
      | X86.Printer.Return i -> handle_instruction instr_num i
      end
  in
  go 0 tail;
  let module Dom = (val state.dom) in
  let pos = Dom.position_of_uid uid in
  state.processed.(pos) <- true;
  List.iter
    (fun pred ->
      if state.processed.(pred) then
        implement_phi_copies state ~src:pred ~dest:pos)
    (Dom.predecessors pos);
  List.iter
    (fun succ ->
      (* todo: use block.succs[0] instead *)
      if state.processed.(succ) then
        implement_phi_copies state ~src:pos ~dest:succ)
    (Dom.successors pos)
