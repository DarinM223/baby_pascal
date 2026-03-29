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
      | X86.Target.Virtual phi ->
        phi.reg <- get_register state (X86.Target.Virtual phi) !occupied;
        occupied := X86.Target.RegSet.add phi.reg !occupied
      | _ -> ())
    phis;
  let handle_instruction instr =
    enforce_constraints state instr;
    (* todo: implement this *)
    ()
  in
  let rec go = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      handle_instruction instr;
      go tail
    | X86.Cfg.Last l ->
      begin match l with
      | X86.Printer.Exit -> ()
      | X86.Printer.Branch (i, _) -> handle_instruction i
      | X86.Printer.CBranch (i, _, _) -> handle_instruction i
      | X86.Printer.Return i -> handle_instruction i
      end
  in
  go tail;
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
