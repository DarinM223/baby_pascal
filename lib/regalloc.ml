type state = {
  regs : X86.Target.reg array;
  num_vars : int;
  processed : bool array;
  preferences : int array array;
  (* initially -1 if no variable for register *)
  reg_current_var : int array;
  (* initially 0 *)
  reg_current_pref : int array;
  liveness : Spill.Liveness.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
}

let get_register state var occupied : int * int =
  let preferences =
    state.preferences.(X86.Target.index var)
    |> Array.mapi (fun i pref -> (i, pref))
  in
  Array.sort (fun (_, pref1) (_, pref2) -> Int.compare pref1 pref2) preferences;
  let exception Reg of int * int in
  try
    for i = Array.length preferences - 1 downto 0 do
      let reg, pref = preferences.(i) in
      if not (CCBV.get occupied reg) then raise (Reg (reg, pref))
    done;
    failwith "get_register: couldn't find non-occupied register"
  with Reg (reg, pref) -> (reg, pref)

let enforce_constraints _state _instr = ()

let implement_phi_copies _state ~src:_ ~dest:_ = ()

let dies state uid a instr_num =
  match state.liveness.dies uid a with
  | Some num when num <= instr_num -> true
  | _ -> false

let color_block state ((first, tail) as block : X86.Cfg.block) : unit =
  let uid = X86.Cfg.id block in
  let occupied = CCBV.create ~size:(Array.length state.regs) false in
  let phis =
    match first with
    | X86.Cfg.Entry -> []
    | X86.Cfg.Label (_, info) -> info.args
  in
  List.iter
    (function
      | X86.Target.Virtual phi' as phi ->
        let reg, pref = get_register state phi occupied in
        phi'.reg <- state.regs.(reg);
        state.reg_current_var.(reg) <- phi'.id;
        state.reg_current_pref.(reg) <- pref;
        CCBV.set occupied reg
      | _ -> ())
    phis;
  let handle_instruction instr_num instr =
    enforce_constraints state instr;
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual a' as a when dies state uid a instr_num ->
          let reg = X86.Target.index a'.reg in
          state.reg_current_var.(reg) <- -1;
          state.reg_current_pref.(reg) <- 0;
          CCBV.reset occupied reg
        | _ -> ())
      (X86.Target.uses instr);
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual r' as r ->
          let reg, pref = get_register state r occupied in
          r'.reg <- state.regs.(reg);
          state.reg_current_var.(reg) <- r'.id;
          state.reg_current_pref.(reg) <- pref;
          CCBV.set occupied reg
        | _ -> ())
      (X86.Target.defs instr)
  in
  let rec go instr_num = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      handle_instruction instr_num instr;
      go (instr_num + 1) tail
    | X86.Cfg.Last l ->
      (* todo: propagate branch args to the affinity chunk *)
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

let build_preferences state graph : int array array =
  let preferences =
    Array.init_matrix state.num_vars (Array.length state.regs) (fun _ _ -> 0)
  in
  let rec handle_operand ?(def = false) live = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand reg; _ }))
      when def ->
      (* add preferences to use variable when there is a reuse operand def *)
      let op = X86.Target.index reg in
      for i = 0 to Array.length preferences.(op) do
        preferences.(op).(i) <- preferences.(op).(i) + preferences.(id).(i)
      done
    | X86.Target.(Reg (Virtual { id; reg_constr = UsePhysical (reg, _, _); _ }))
      ->
      (* give penalties to all registers that are not the constrained register. *)
      for i = 0 to Array.length preferences.(id) do
        if i <> reg then preferences.(id).(i) <- preferences.(id).(i) - 1
      done;
      (* give penalties to all other live variables for the constrained register *)
      CCBV.iter_true live (fun live ->
          if live <> id then
            preferences.(live).(reg) <- preferences.(live).(reg) - 1)
    | X86.Target.Label (_, ops) -> List.iter (handle_operand live) ops
    | _ -> ()
  in
  let handle_instruction live (instr : X86.Target.instr) =
    List.iter (handle_operand ~def:true live) instr.defs;
    (* todo: handle reuse_op constraints for defs here by adding the preferences to the use *)
    let defs =
      X86.Target.defs instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.diff_into ~into:live defs;
    List.iter (handle_operand live) instr.uses;
    let uses =
      X86.Target.uses instr |> X86.Target.RegSet.to_list
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.union_into ~into:live uses
  in
  let go_block block =
    let live_out = state.liveness.live_out (X86.Cfg.id block) in
    let live =
      CCBV.of_list
        (List.map X86.Target.index (X86.Target.RegSet.to_list live_out))
    in
    let head, last = X86.Cfg.(goto_end (unzip block)) in
    begin match last with
    | X86.Printer.Exit -> ()
    | X86.Printer.Branch (i, _) -> handle_instruction live i
    | X86.Printer.CBranch (i, _, _) -> handle_instruction live i
    | X86.Printer.Return i -> handle_instruction live i
    end;
    let rec go_head = function
      | X86.Cfg.Head (head, Instruction i) ->
        handle_instruction live i;
        go_head head
      | X86.Cfg.First _ -> () (* ignore phis *)
    in
    go_head head
  in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter go_block rpo;
  preferences

let create_congruence_class _state _classes _block =
  (* for each jump arg: *)
  (* interferes if anything in live_in of block successor has the same set representative as jump arg *)
  (* interferes if other args in jump has same set representative as jump arg *)
  (* if no interference, merge jump arg and successor phi classes and add preferences to set representative *)
  (* for each instruction: *)
  (* update liveness at current point in block *)
  (* if defined variable has reuse operand constraint: *)
  (* if any current live variables has the same set representative as the reused operand then it interferes *)
  (* if no interference then merge classes for reuse operand def and use variables *)
  failwith ""

let set_congruence_prefs state classes v =
  let v_repr = Unionfind.(to_int (find classes v)) in
  if v <> v_repr then
    Array.blit state.preferences.(v_repr) 0 state.preferences.(v) 0
      (Array.length state.preferences.(v))

let combine_congruence_classes state graph =
  let classes = Unionfind.create state.num_vars in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter (create_congruence_class state classes) rpo;
  Array.iteri
    (fun v _ -> set_congruence_prefs state classes v)
    state.preferences
