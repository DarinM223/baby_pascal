module RegSet = Spill.Liveness.RegSet
module RegMap = Spill.Liveness.RegMap

module Weights = struct
  let use_factor = 1.
  let def_factor = 1.
  let neighbor_factor = 0.2
  let aff_should_be_same = 0.5
  let aff_phi = 1.
end

type state = {
  select_state : Select_x86.State.t;
  regs : X86.Target.reg array;
  num_vars : int;
  processed : bool array;
  block_execution_frequency : X86.Cfg.uid -> float;
  preferences : float array CCVector.vector;
  reg_current_var : X86.Target.virtual_reg option array;
  (* initially 0 *)
  reg_current_pref : float array;
  liveness : Spill.Liveness.t;
  occupied : CCBV.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
  mutable subst : X86.Target.reg RegMap.t;
}

let ( .%() ) = CCVector.get

let pp_preferences regs fmt preferences =
  let open Format in
  pp_open_box fmt 0;
  pp_print_string fmt "[";
  for i = 0 to CCVector.length preferences - 1 do
    pp_print_int fmt i;
    pp_print_string fmt " -> ";
    pp_open_box fmt 0;
    pp_print_string fmt "[";
    for j = 0 to Array.length preferences.%(i) - 1 do
      let reg = regs.(j) in
      let pref = preferences.%(i).(j) in
      printf "%a: %f" X86.Target.pp_reg reg pref;
      if j <> Array.length preferences.%(i) - 1 then pp_print_string fmt ", "
    done;
    pp_print_string fmt "]";
    pp_close_box fmt ();
    if i <> CCVector.length preferences - 1 then pp_print_string fmt ", "
  done;
  pp_print_string fmt "]";
  pp_close_box fmt ()

let find_reg_index regs reg : int =
  match CCArray.find_idx (X86.Target.equal_reg reg) regs with
  | Some (index, _) -> index
  | None ->
    failwith
      (Format.asprintf "find_reg: couldn't find index for register %a"
         X86.Target.pp_reg reg)

let get_register state uid var head : int * float * X86.Cfg.head =
  (* give preference bonus to ReuseOperand contraints *)
  begin match var with
  | X86.Target.Virtual { reg_constr = ReuseOperand (Virtual r); _ } ->
    let weight = state.block_execution_frequency uid in
    let reg_index = find_reg_index state.regs r.reg in
    state.preferences.%(X86.Target.index var).(reg_index) <-
      state.preferences.%(X86.Target.index var).(reg_index)
      +. (weight *. Weights.aff_should_be_same)
  | _ -> ()
  end;
  let preferences =
    state.preferences.%(X86.Target.index var)
    |> Array.mapi (fun i pref -> (i, pref))
  in
  Logs.debug (fun m ->
      m "Preferences for %a are: %a\n" X86.Target.pp_reg var
        (pp_preferences state.regs)
        (CCVector.of_array [| Array.map snd preferences |]));
  Array.sort
    (fun (_, pref1) (_, pref2) -> Float.compare pref1 pref2)
    preferences;
  let exception Reg of int * float * X86.Cfg.head in
  let exception Break of int * float in
  try
    for i = Array.length preferences - 1 downto 0 do
      let reg, pref = preferences.(i) in
      if not (CCBV.get state.occupied reg) then raise (Reg (reg, pref, head));
      let ovar = Option.get state.reg_current_var.(reg) in
      let preferences =
        Array.mapi (fun i pref -> (i, pref)) state.preferences.%(ovar.id)
      in
      Array.sort
        (fun (_, pref1) (_, pref2) -> Float.compare pref1 pref2)
        preferences;
      try
        for i = Array.length preferences - 1 downto 0 do
          let oreg, opref = preferences.(i) in
          if not (CCBV.get state.occupied oreg) then
            raise (Break (oreg, opref -. state.reg_current_pref.(oreg)))
        done
      with Break (oreg, other_win) ->
        if i + 1 < Array.length preferences then
          let _, next_pref = preferences.(i + 1) in
          let win = next_pref -. pref in
          if win +. other_win > state.block_execution_frequency uid then begin
            Logs.debug (fun m ->
                m "Adding move from %a to %a" X86.Target.pp_reg state.regs.(reg)
                  X86.Target.pp_reg state.regs.(oreg));
            let mov =
              X86.Target.mov
                ~dest:(Reg state.regs.(oreg))
                ~src:(Reg state.regs.(reg))
            in
            let head = X86.Cfg.Head (head, Instruction mov) in
            raise (Reg (reg, pref, head))
          end
    done;
    failwith "get_register: couldn't find non-occupied register"
  with Reg (reg, pref, head) ->
    Logs.debug (fun m -> m "Found reg: %a\n" X86.Target.pp_reg state.regs.(reg));
    (reg, pref, head)

let dies state uid a instr_num =
  match state.liveness.dies uid a with
  | Some num when num <= instr_num -> true
  | _ -> false

module type EnforceConstraints = sig
  val dest_mapping : X86.Target.reg array
  (** Mapping from register to destination register in original instruction.
      Used for reusing existing virtual registers in the original pcopy. *)

  val live_through_regs : CCBV.t
  (** Registers that are currently being occupied by values that live through
      the instruction occupied regs - regs that die at the instruction *)

  val constrained_def_regs : CCBV.t
  (** Registers that are constrained in parallel copy definitions without a
      corresponding use. These registers will be clobbered after the
      instruction, similarly to caller-save registers after a call. *)

  val need_swap : CCBV.t
  (** Registers that currently contain a live through value *)

  val need_reassignment : bool
  (** True if a parallel copy shuffling the registers to fit the constraints is
      necessary *)
end

let enforce_constraints_state state uid instr_num instr =
  let num_regs = Array.length state.regs in
  (* Mapping from register to destination register in original instruction.
     Used for reusing existing virtual registers in the original pcopy. *)
  let dest_mapping = Array.make num_regs X86.Target.Tombstone in
  (* Registers that are currently being occupied by values
     that live through the instruction
     occupied regs - regs that die at the instruction *)
  let live_through_regs = CCBV.copy state.occupied in
  let constrained_def_regs = CCBV.create ~size:num_regs false in
  let need_swap = CCBV.create ~size:num_regs false in
  let need_reassignment = ref false in
  let remove_constrained_use_live_throughs = function
    | (X86.Target.Virtual a' as a), _ when dies state uid a instr_num ->
      let reg = find_reg_index state.regs a'.reg in
      Logs.debug (fun m ->
          m "Removing %a from live throughs\n" X86.Target.pp_reg
            state.regs.(reg));
      CCBV.reset live_through_regs reg
    | ( X86.Target.Virtual a',
        ( X86.Target.Virtual { reg_constr = UsePhysical _; _ }
        | X86.Target.Physical _ ) ) ->
      let reg = find_reg_index state.regs a'.reg in
      CCBV.set need_swap reg
    | _ -> ()
  in
  let mark_constrained_def_regs = function
    | ( X86.Target.Virtual { reg_constr = UsePhysical phys; _ }
      | X86.Target.Physical phys ) as r ->
      begin try
        let reg_index = find_reg_index state.regs (Physical phys) in
        Logs.debug (fun m ->
            m "Setting %a as constrained def\n" X86.Target.pp_reg
              state.regs.(reg_index));
        CCBV.set constrained_def_regs reg_index;
        dest_mapping.(reg_index) <- r;
        if CCBV.get live_through_regs reg_index then need_reassignment := true
      with _ -> ()
      end
    | _ -> ()
  in
  let rec go_uses_defs = function
    | X86.Target.Reg use :: uses, X86.Target.Reg def :: defs ->
      (* todo: swap if use is in a live through register and the def is in a constrained def register *)
      if use <> Tombstone && def <> Tombstone then begin
        remove_constrained_use_live_throughs (use, def)
      end;
      go_uses_defs (uses, defs)
    | _ :: uses, _ :: defs -> go_uses_defs (uses, defs)
    | [], X86.Target.Reg def :: defs ->
      if def <> Tombstone then mark_constrained_def_regs def;
      go_uses_defs ([], defs)
    | _ -> ()
  in
  go_uses_defs (instr.X86.Target.uses, instr.defs);
  CCBV.iter_true live_through_regs (fun reg ->
      Logs.debug (fun m ->
          m "Live through: %a\n" X86.Target.pp_reg state.regs.(reg)));
  let module EnforceConstraints = struct
    let dest_mapping = dest_mapping
    let live_through_regs = live_through_regs
    let constrained_def_regs = constrained_def_regs
    let need_swap = need_swap
    let need_reassignment = !need_reassignment
  end in
  (module EnforceConstraints : EnforceConstraints)

(** Unlike in the normal preference based register allocation algorithm, enforce
    constraints are only enforced on parallel copies. Constrained uses are uses
    in the pcopy that have a corresponding def, constrained defs are definitions
    at the end which don't have a corresponding use. *)
let enforce_constraints_pcopy (module State : EnforceConstraints) state uid
    instr_num instr =
  let num_regs = Array.length state.regs in
  let open State in
  let cost = Array.make (num_regs * num_regs) 0 in
  for l = 0 to num_regs - 1 do
    for r = 0 to num_regs - 1 do
      if
        (* Don't move a constrained def register
             into a live through register that isn't a constrained def register
             That would clobber a live through register like a callee save register *)
        CCBV.get live_through_regs l
        && (not (CCBV.get constrained_def_regs l))
        && CCBV.get constrained_def_regs r
      then
        Logs.debug (fun m ->
            m "No edge from %a to %a" X86.Target.pp_reg state.regs.(r)
              X86.Target.pp_reg state.regs.(l))
      else if
        (* Don't move a live through value that currently occupies a
             constrained def register into another constrained def register
             That register will be clobbered and won't live through the instruction *)
        CCBV.get constrained_def_regs l
        && CCBV.get live_through_regs r
        && CCBV.get constrained_def_regs r
      then
        Logs.debug (fun m ->
            m "No edge from %a to %a" X86.Target.pp_reg state.regs.(r)
              X86.Target.pp_reg state.regs.(l))
      else cost.((l * num_regs) + r) <- (if l = r then 8 else 7)
    done
  done;
  (* Remove edges from constrained use virtual registers to non-constrained registers
       In other words, you can only move a constrained use to the register in the constraint,
       not to any other register *)
  let remove_constrained_use_edges = function
    | ( X86.Target.Virtual { reg; _ },
        (X86.Target.Virtual { reg_constr = UsePhysical phys; _ } as vreg) ) ->
      let curr_reg = find_reg_index state.regs reg in
      let constraint_reg = find_reg_index state.regs (Physical phys) in
      dest_mapping.(constraint_reg) <- vreg;
      for r = 0 to num_regs - 1 do
        if r <> constraint_reg then cost.((r * num_regs) + curr_reg) <- 0
        else cost.((r * num_regs) + curr_reg) <- 9
      done
    | _ -> ()
  in
  let rec go_constrained_uses = function
    | X86.Target.Reg use :: uses, X86.Target.Reg def :: defs ->
      remove_constrained_use_edges (use, def);
      go_constrained_uses (uses, defs)
    | _ -> ()
  in
  go_constrained_uses (instr.X86.Target.uses, instr.defs);
  Hungarian.min_to_max_cost ~max_cost:9 cost;
  Logs.debug (fun m ->
      m "Cost matrix: \n%a\n"
        (Hungarian.pp_cost ~assignment:None ~regs:state.regs ~num_rows:num_regs
           ~num_cols:num_regs)
        cost);
  let permutation =
    Hungarian.solve ~cost ~num_rows:num_regs ~num_cols:num_regs
  in
  Logs.debug (fun m ->
      m "Assignment: %a\n"
        (Hungarian.pp_assignment ~regs:state.regs)
        permutation);
  Logs.debug (fun m ->
      m "Cost matrix: \n%a\n"
        (Hungarian.pp_cost ~assignment:(Some permutation) ~regs:state.regs
           ~num_rows:num_regs ~num_cols:num_regs)
        cost);
  (* After, the index of permutation is the destination register
       and the value is the source register *)
  let srcs = ref [] in
  let dests = ref [] in
  let subst = ref RegMap.empty in
  let dest_reg_dies_immediately = Array.make num_regs false in
  for dest = 0 to num_regs - 1 do
    let old_reg = permutation.(dest) in
    match state.reg_current_var.(old_reg) with
    | Some src ->
      state.reg_current_var.(old_reg) <- None;
      state.reg_current_pref.(old_reg) <- 0.;
      CCBV.reset state.occupied old_reg;
      srcs := X86.Target.(Reg (Virtual src)) :: !srcs;
      (* If you can't reuse an existing definition virtual register,
           create a new virtual register constrained to the destination
           register and substitute it for every following use of the
           source register. *)
      dest_mapping.(dest) <-
        begin match dest_mapping.(dest) with
        | Tombstone ->
          let phys =
            match state.regs.(dest) with
            | Physical phys -> phys
            | _ -> failwith "expected physical register in regs"
          in
          let vreg =
            X86.Target.constrained phys (state.select_state.fresh_vreg Int)
          in
          CCVector.push state.preferences state.preferences.%(src.id);
          vreg
        | r -> r
        end;
      (* If register is live-through and it isn't a
           constrained definition register, then it will still be accessible
           after this instruction, so don't add it as a substitution. *)
      if
        let src_reg = find_reg_index state.regs src.reg in
        CCBV.get constrained_def_regs src_reg
        || not (CCBV.get live_through_regs src_reg)
      then subst := RegMap.add (Virtual src) dest_mapping.(dest) !subst;
      dest_reg_dies_immediately.(dest) <- dies state uid (Virtual src) instr_num;
      dests := X86.Target.Reg dest_mapping.(dest) :: !dests
    | None -> ()
  done;
  for dest = 0 to num_regs - 1 do
    match dest_mapping.(dest) with
    | Virtual vreg ->
      vreg.reg <- state.regs.(dest);
      state.reg_current_var.(dest) <- Some vreg;
      (* Preferences array doesn't this virtual register's id because it is newly created *)
      state.reg_current_pref.(dest) <- 0.;
      if not dest_reg_dies_immediately.(dest) then CCBV.set state.occupied dest
    | _ -> ()
  done;
  Logs.debug (fun m ->
      m "Shuffling Dests: %a Srcs: %a\n" X86.Target.pp_operands !dests
        X86.Target.pp_operands !srcs);
  (X86.Target.pcopy ~dests:!dests ~srcs:!srcs, !subst)

let enforce_constraints state uid instr_num instr head =
  let s = enforce_constraints_state state uid instr_num instr in
  let module State = (val s) in
  if not State.need_reassignment then head
  else
    let pcopy, subst = enforce_constraints_pcopy s state uid instr_num instr in
    state.subst <- RegMap.union (fun _ v _ -> Some v) subst state.subst;
    X86.Cfg.Head (head, Instruction pcopy)

(* Insert parallel copy instruction in src block to move arguments
   to assigned registers in dest block. *)
let implement_phi_copies state cfg ~src ~dest =
  let module Dom = (val state.dom) in
  let dest_label = Dom.label_of_position dest in
  let zblock, cfg = X86.Cfg.(focus (idd (Dom.label_of_position src)) cfg) in
  let head, last = X86.Cfg.goto_end zblock in
  let get_args instr =
    instr.X86.Target.uses
    |> List.find_map (function
      | X86.Target.Label (label, args) when dest_label = Some label -> Some args
      | _ -> None)
    |> Option.value ~default:[]
  in
  let replace_args instr args =
    {
      instr with
      X86.Target.uses =
        List.map
          (function
            | X86.Target.Label (label, _) when dest_label = Some label ->
              X86.Target.Label (label, args)
            | op -> op)
          instr.X86.Target.uses;
    }
  in
  let args =
    match last with
    | X86.Printer.Exit -> []
    | X86.Printer.Branch (instr, _) -> get_args instr
    | X86.Printer.CBranch (instr, _, _) -> get_args instr
    | X86.Printer.Return _ -> []
  in
  let phis =
    match X86.Cfg.(first (fst (focus (idd dest_label) cfg))) with
    | X86.Cfg.Label (_, info) -> info.args
    | X86.Cfg.Entry -> []
  in
  let srcs, dests, args =
    let open X86.Target in
    List.fold_right
      (fun (arg, phi) (srcs, dests, args) ->
        match (arg, phi) with
        | Reg (Virtual { reg = arg_reg; _ }), Virtual { reg = phi_reg; _ }
          when X86.Target.equal_reg arg_reg phi_reg ->
          (srcs, dests, arg :: args)
        | Reg (Virtual varg), Virtual { reg = Physical phi_reg; _ } ->
          let copy =
            Reg (constrained phi_reg (state.select_state.fresh_vreg Int))
          in
          CCVector.push state.preferences state.preferences.%(varg.id);
          (arg :: srcs, copy :: dests, copy :: args)
        | _ -> failwith "Phi not a virtual register")
      (List.combine args phis) ([], [], [])
  in
  let last =
    match last with
    | X86.Printer.Exit -> last
    | X86.Printer.Branch (instr, l) ->
      X86.Printer.Branch (replace_args instr args, l)
    | X86.Printer.CBranch (instr, l1, l2) ->
      X86.Printer.CBranch (replace_args instr args, l1, l2)
    | X86.Printer.Return _ -> last
  in
  let tail =
    let open X86 in
    if List.length dests > 0 then
      Cfg.Tail (Cfg.Instruction (Target.pcopy ~dests ~srcs), Cfg.Last last)
    else Cfg.Last last
  in
  X86.Cfg.unfocus ((head, tail), cfg)

let color_block state ((first, tail) as block : X86.Cfg.block) : X86.Cfg.block =
  let uid = X86.Cfg.id block in
  let phis =
    match first with
    | X86.Cfg.Entry -> []
    | X86.Cfg.Label (_, info) -> info.args
  in
  let head =
    List.fold_left
      (fun head -> function
        | X86.Target.Virtual phi' as phi when X86.Target.equal_reg phi'.reg phi
          ->
          let reg, pref, head = get_register state uid phi head in
          phi'.reg <- state.regs.(reg);
          state.reg_current_var.(reg) <- Some phi';
          state.reg_current_pref.(reg) <- pref;
          CCBV.set state.occupied reg;
          head
        | _ -> head)
      (X86.Cfg.First first) phis
  in
  let handle_instruction instr_num head instr =
    let subst_reg reg = RegMap.get_or ~default:reg reg state.subst in
    let instr = X86.Target.(map_uses (subst_reg_operand subst_reg)) instr in
    let head =
      if instr.X86.Target.instr = "pcopy" then
        enforce_constraints state uid instr_num instr head
      else head
    in
    X86.Target.RegSet.iter
      (function
        | X86.Target.Virtual a' as a when dies state uid a instr_num ->
          let reg = find_reg_index state.regs a'.reg in
          state.reg_current_var.(reg) <- None;
          state.reg_current_pref.(reg) <- 0.;
          CCBV.reset state.occupied reg
        | _ -> ())
      (X86.Target.uses instr);
    X86.Target.RegSet.fold
      (function
        | X86.Target.Virtual r' as r when X86.Target.equal_reg r'.reg r ->
          fun head ->
            let reg, pref, head = get_register state uid r head in
            r'.reg <- state.regs.(reg);
            state.reg_current_var.(reg) <- Some r';
            state.reg_current_pref.(reg) <- pref;
            if not (dies state uid r instr_num) then CCBV.set state.occupied reg;
            head
        | _ -> fun head -> head)
      (X86.Target.defs instr) head
  in
  let rec go instr_num head = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      let head = handle_instruction instr_num head instr in
      go (instr_num + 1) (X86.Cfg.Head (head, Instruction instr)) tail
    | X86.Cfg.Last l ->
      (* todo: propagate branch args to the affinity chunk *)
      let head =
        match l with
        | X86.Printer.Exit -> head
        | X86.Printer.Branch (i, _) -> handle_instruction instr_num head i
        | X86.Printer.CBranch (i, _, _) -> handle_instruction instr_num head i
        | X86.Printer.Return i -> handle_instruction instr_num head i
      in
      (head, X86.Cfg.Last l)
  in
  let block = X86.Cfg.zip (go 0 head tail) in
  let module Dom = (val state.dom) in
  let pos = Dom.position_of_uid uid in
  state.processed.(pos) <- true;
  block

let after_color_block state (cfg : X86.Cfg.graph) pos : X86.Cfg.graph =
  let module Dom = (val state.dom) in
  let cfg =
    List.fold_left
      (fun cfg pred ->
        if state.processed.(pred) then
          implement_phi_copies state cfg ~src:pred ~dest:pos
        else cfg)
      cfg (Dom.predecessors pos)
  in
  List.fold_left
    (fun cfg succ ->
      (* todo: use block.succs[0] instead *)
      if state.processed.(succ) then
        implement_phi_copies state cfg ~src:pos ~dest:succ
      else cfg)
    cfg (Dom.successors pos)

let build_preferences state graph : unit =
  let preferences = state.preferences in
  let rec handle_operand ?(def = false) uid live = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand reg; _ }))
      when def ->
      (* add preferences to use variable when there is a reuse operand def *)
      let op = X86.Target.index reg in
      for i = 0 to Array.length preferences.%(op) - 1 do
        preferences.%(op).(i) <- preferences.%(op).(i) +. preferences.%(id).(i)
      done
    | X86.Target.(Reg (Virtual { id; reg_constr = UsePhysical phys; _ })) ->
      begin try
        let reg = find_reg_index state.regs (X86.Target.Physical phys) in
        let weight = state.block_execution_frequency uid in
        let penalty =
          weight *. if def then Weights.def_factor else Weights.use_factor
        in
        (* give penalties to all registers that are not the constrained register. *)
        for i = 0 to Array.length preferences.%(id) - 1 do
          if i <> reg then
            preferences.%(id).(i) <- preferences.%(id).(i) -. penalty
        done;
        let penalty = penalty *. Weights.neighbor_factor in
        (* give penalties to all other live variables for the constrained register *)
        CCBV.iter_true live (fun live ->
            if live <> id then
              preferences.%(live).(reg) <- preferences.%(live).(reg) -. penalty)
      with _ -> ()
      end
    | X86.Target.Label (_, ops) -> List.iter (handle_operand uid live) ops
    | _ -> ()
  in
  let handle_instruction uid live (instr : X86.Target.instr) =
    List.iter (handle_operand ~def:true uid live) instr.defs;
    let defs =
      X86.Target.defs instr |> X86.Target.RegSet.elements
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.diff_into ~into:live defs;
    List.iter (handle_operand uid live) instr.uses;
    let uses =
      X86.Target.uses instr |> X86.Target.RegSet.elements
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.union_into ~into:live uses
  in
  let go_block block =
    let uid = X86.Cfg.id block in
    let live_out = state.liveness.live_out uid in
    let live =
      CCBV.of_list
        (List.map X86.Target.index (X86.Target.RegSet.elements live_out))
    in
    let head, last = X86.Cfg.(goto_end (unzip block)) in
    begin match last with
    | X86.Printer.Exit -> ()
    | X86.Printer.Branch (i, _) -> handle_instruction uid live i
    | X86.Printer.CBranch (i, _, _) -> handle_instruction uid live i
    | X86.Printer.Return i -> handle_instruction uid live i
    end;
    let rec go_head = function
      | X86.Cfg.Head (head, Instruction i) ->
        handle_instruction uid live i;
        go_head head
      | X86.Cfg.First _ -> () (* ignore phis *)
    in
    go_head head
  in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter go_block rpo

let create_congruence_class state classes graph block =
  let live =
    let live_out = state.liveness.live_out (X86.Cfg.id block) in
    CCBV.of_list
      (List.map X86.Target.index (X86.Target.RegSet.elements live_out))
  in
  let liveness_transfer instr =
    let defs =
      X86.Target.defs instr |> X86.Target.RegSet.elements
      |> List.map X86.Target.index |> CCBV.of_list
    in
    let uses =
      X86.Target.uses instr |> X86.Target.RegSet.elements
      |> List.map X86.Target.index |> CCBV.of_list
    in
    CCBV.diff_into ~into:live defs;
    CCBV.union_into ~into:live uses
  in
  let handle_jump_arg succ args i arg =
    let succ = X86.Cfg.idd (Some succ) in
    let live = state.liveness.live_in succ in
    let check_interferes v =
      Unionfind.equal_repr
        (Unionfind.find classes (X86.Target.index v))
        (Unionfind.find classes (X86.Target.index arg))
    in
    (* interferes if anything in live_in of block successor has the same set representative as jump arg
       or if other args in jump has same set representative as jump arg *)
    let interferes =
      RegSet.exists check_interferes live
      || args
         |> List.filter_map (function
           | X86.Target.Reg r when not (X86.Target.equal_reg r arg) -> Some r
           | _ -> None)
         |> List.exists check_interferes
    in
    (* if no interference, merge jump arg and successor phi classes and add preferences to set representative *)
    if not interferes then
      let phi =
        match X86.Cfg.(first (fst (focus succ graph))) with
        | X86.Cfg.Entry ->
          failwith "create_congruence_class: jump with arguments to entry block"
        | X86.Cfg.Label (_, info) ->
          begin match List.nth_opt info.args i with
          | Some phi -> phi
          | None ->
            failwith "create_congruence_class: jump has different arity to phis"
          end
      in
      let arg_repr = Unionfind.find classes (X86.Target.index arg) in
      let phi_repr = Unionfind.find classes (X86.Target.index phi) in
      let merged_repr = Unionfind.union classes arg_repr phi_repr in
      let other_repr =
        if Unionfind.equal_repr merged_repr phi_repr then arg_repr else phi_repr
      in
      let merged = state.preferences.%(Unionfind.to_int merged_repr) in
      let other = state.preferences.%(Unionfind.to_int other_repr) in
      for r = 0 to Array.length state.regs - 1 do
        merged.(r) <- merged.(r) +. other.(r)
      done
  in
  let handle_jump instr =
    List.iter
      (function
        | X86.Target.Label (succ, args) ->
          List.iteri
            (fun i -> function
              | X86.Target.Reg r -> handle_jump_arg succ args i r
              | _ -> ())
            args
        | _ -> ())
      instr.X86.Target.uses
  in
  let head, last = X86.Cfg.(goto_end (unzip block)) in
  begin match last with
  | X86.Printer.Exit -> ()
  | X86.Printer.Branch (instr, _) ->
    handle_jump instr;
    liveness_transfer instr
  | X86.Printer.CBranch (instr, _, _) ->
    handle_jump instr;
    liveness_transfer instr
  | X86.Printer.Return instr -> liveness_transfer instr
  end;
  let handle_reuse_operand_def = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand op; _ })) ->
      let op = X86.Target.index op in
      let interferes = ref false in
      let exception Break in
      (* if any current live variables has the same set representative as the reused operand then it interferes *)
      begin try
        CCBV.iter_true live @@ fun v ->
        if Unionfind.(equal_repr (find classes v) (find classes op)) then begin
          interferes := true;
          raise Break
        end
      with Break -> ()
      end;
      (* if no interference then merge classes for reuse operand def and use variables *)
      if not !interferes then
        ignore Unionfind.(union classes (find classes id) (find classes op))
    | _ -> ()
  in
  let rec go_head = function
    | X86.Cfg.First _ -> ()
    | X86.Cfg.Head (head, Instruction instr) ->
      List.iter handle_reuse_operand_def instr.defs;
      liveness_transfer instr;
      go_head head
  in
  go_head head

let set_congruence_prefs state classes v =
  let v_repr = Unionfind.(to_int (find classes v)) in
  if v <> v_repr then
    Array.blit
      state.preferences.%(v_repr)
      0 state.preferences.%(v) 0
      (Array.length state.preferences.%(v))

let combine_congruence_classes state graph =
  let classes = Unionfind.create state.num_vars in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter (create_congruence_class state classes graph) rpo;
  CCVector.iteri
    (fun v _ -> set_congruence_prefs state classes v)
    state.preferences

let rec add_trace (module Dom : Dominator.S with type position = int) trace seen
    order block =
  if not seen.(block) then begin
    let best_pred =
      Dom.predecessors block
      |> List.filter (fun pred -> not (Dom.dominates block pred))
      |> List.fold_left
           (function
             | None -> fun pred -> Some pred
             | Some best ->
               fun pred ->
                 Some (if trace.(best) < trace.(pred) then pred else best))
           None
    in
    let order =
      match best_pred with
      | Some pred -> add_trace (module Dom) trace seen order pred
      | None -> order
    in
    seen.(block) <- true;
    block :: order
  end
  else order

let blockorder state =
  let module Dom = (val state.dom) in
  let trace = Array.make Dom.size 0. in
  for b = Dom.size - 1 downto 0 do
    let uid = X86.Cfg.idd (Dom.label_of_position b) in
    let t =
      List.fold_left
        (fun acc pred -> max acc trace.(pred))
        0. (Dom.predecessors b)
    in
    trace.(b) <- t +. state.block_execution_frequency uid
  done;
  let blocks = Array.init Dom.size (fun i -> i) in
  Array.sort (fun a b -> Float.compare trace.(a) trace.(b)) blocks;
  let seen = Array.make Dom.size false in
  List.rev @@ Array.fold_left (add_trace (module Dom) trace seen) [] blocks

module IntHashtbl = Utils.IntHashtbl

let reg_ops =
  List.filter_map (function
    | X86.Target.Reg r -> Some r
    | _ -> None)

let spill_helper ?(args = [])
    (module Loop : Loopnesting.S
      with type Dom.label = X86.Cfg.label
       and type Dom.position = int
       and type Dom.uid = int) state cfg =
  let next_use_distances = Spill.next_use_distances (module Loop) cfg in
  let liveness = Spill.Liveness.calc cfg in
  let module Spill' =
    Spill.Make
      (Loop)
      (struct
        let k = 16
        let next_use_distances = next_use_distances
        let liveness = liveness
      end) in
  let spill_state = Spill'.init state in
  let cfg = Spill'.spill ~args spill_state cfg in
  let module Reconstruct = Reconstruct.Make (X86.Target) (X86.Cfg) (Loop.Dom) in
  let reconstruct_copies reg _ graph =
    let copies = Spill'.RegHashtbl.find_all spill_state.copies reg in
    let def_blocks =
      List.map
        (fun r ->
          Deadcode.IntHashtbl.find spill_state.select_state.vreg_block
            (X86.Target.index r))
        (reg :: copies)
    in
    Reconstruct.reconstruct
      (fun () -> spill_state.select_state.fresh_vreg Int)
      (Spill'.RegSet.singleton reg)
      (Spill'.RegSet.of_list copies)
      def_blocks graph
  in
  Spill'.RegHashtbl.fold reconstruct_copies spill_state.copies cfg

let init_state ~select_state ~regs ~block_execution_frequency ~liveness
    (module Dom : Dominator.S
      with type label = X86.Cfg.label
       and type position = int
       and type uid = int
       and type graph = X86.Cfg.graph) =
  let num_vars = IntHashtbl.length select_state.Select_x86.State.vreg_block in
  {
    select_state;
    regs;
    block_execution_frequency;
    liveness;
    dom = (module Dom);
    reg_current_var = Array.make (Array.length regs) None;
    reg_current_pref = Array.make (Array.length regs) 0.;
    processed = Array.make Dom.size false;
    num_vars;
    preferences =
      CCVector.init num_vars (fun _ -> Array.make (Array.length regs) 0.);
    occupied = CCBV.create ~size:(Array.length regs) false;
    subst = RegMap.empty;
  }

let regalloc_helper ?(args = RegSet.empty)
    ?(regs =
      X86.Regs.int_regs |> Array.of_list
      |> Array.map (fun r -> X86.Target.Physical r))
    (module Loop : Loopnesting.S
      with type Dom.label = X86.Cfg.label
       and type Dom.position = int
       and type Dom.uid = int
       and type Dom.graph = X86.Cfg.graph) state cfg k_prefs =
  (* have to recalculate because added spills may have modified the instruction numbers *)
  let liveness = Spill.Liveness.calc cfg in
  let module Freq = Execfreq.Make (X86.Cfg) (Loop) (X86.ExecfreqRequirements) in
  let block_execution_frequency uid =
    Freq.bfreq.(Loop.Dom.position_of_uid uid)
  in
  let alloc_state =
    init_state ~select_state:state ~block_execution_frequency ~liveness ~regs
      (module Loop.Dom)
  in
  build_preferences alloc_state cfg;
  combine_congruence_classes alloc_state cfg;
  k_prefs alloc_state;
  let go_block cfg pos =
    let uid = X86.Cfg.idd (Loop.Dom.label_of_position pos) in
    alloc_state.select_state.curr_block := uid;
    let zblock, cfg = X86.Cfg.focus uid cfg in
    let zblock =
      if uid = X86.Cfg.entry_uid then
        let head, tail = zblock in
        let head =
          RegSet.fold
            (function
              | X86.Target.Virtual r' as r when X86.Target.equal_reg r'.reg r ->
                fun head ->
                  let reg, pref, head =
                    get_register alloc_state X86.Cfg.entry_uid r head
                  in
                  r'.reg <- alloc_state.regs.(reg);
                  alloc_state.reg_current_var.(reg) <- Some r';
                  alloc_state.reg_current_pref.(reg) <- pref;
                  CCBV.set alloc_state.occupied reg;
                  head
              | _ -> fun head -> head)
            args head
        in
        (head, tail)
      else zblock
    in
    let block = color_block alloc_state (X86.Cfg.zip zblock) in
    let cfg = X86.Cfg.(unfocus (unzip block, cfg)) in
    after_color_block alloc_state cfg pos
  in
  List.fold_left go_block cfg (blockorder alloc_state)

let%expect_test "Nested loops register allocation" =
  let cfg = Examples.nested_loops in
  let state = Select_x86.State.init () in
  let _, cfg = Select_x86.codegen_test_helper state cfg in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let cfg = spill_helper (module Loop) state cfg in
  let cfg =
    regalloc_helper (module Loop) state cfg @@ fun state ->
    Format.printf "%a\n" (pp_preferences state.regs) state.preferences;
    [%expect
      {|
    [0 -> [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 1 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 2 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 3 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 4 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 5 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 6 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 7 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 8 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 9 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 10 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000]]
    |}]
  in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      movq %rax(0), $0
      jmp label6
    label1(local=false)():
      exit
    label2(local=false)(rax(1)):
      jl label3, label1, %rax(1), $100
    label3(local=false)():
      movq %rbx(2), %rax(1)
      jmp label4(%rax(1), %rbx(2))
    label4(local=false)(rax(3), rbx(4)):
      jl label5, label2(%rax(3)), %rbx(4), $100
    label5(local=false)():
      movq %rax(7), %rax(3)
      addq %rax(6), %rax(7), $1
      movq %rax(5), %rax(6)
      movq %rbx(10), %rbx(4)
      addq %rbx(9), %rbx(10), $1
      movq %rbx(8), %rbx(9)
      jmp label4(%rax(5), %rbx(8))
    label6(local=false)():
      jmp label2(%rax(0))
    |}]

let%expect_test "Fibonacci register allocation" =
  let cfg = Examples.fibonacci in
  let state = Select_x86.State.init () in
  let srcs, cfg = Select_x86.codegen_test_helper ~args:[ "v" ] state cfg in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let cfg = spill_helper ~args:(reg_ops srcs) (module Loop) state cfg in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      pcopy [(%1any, %0(%rdi))]
      jle label2, label3, %1any, $1
    label1(local=false)(32any):
      movq %33(%rax), %32any
      ret %33(%rax)
    label2(local=false)():
      movq %2any, %1any
      jmp label1(%2any)
    label3(local=false)():
      movq %5any, %1any
      subq %4(reuse=%5), %5any, $1
      pcopy [(%6(%rdi), %4(reuse=%5)); (%7(%rax), %); (%8(%rcx), %);
              (%9(%rdx), %); (%10(%rsi), %); (%11(%rdi), %); (%12(%r8), %);
              (%13(%r9), %); (%14(%r10), %); (%15(%r11), %)]
      call fibonacci
      movq %3any, %7(%rax)
      movq %18any, %1any
      subq %17(reuse=%18), %18any, $2
      pcopy [(%19(%rdi), %17(reuse=%18)); (%20(%rax), %); (%21(%rcx), %);
              (%22(%rdx), %); (%23(%rsi), %); (%24(%rdi), %); (%25(%r8), %);
              (%26(%r9), %); (%27(%r10), %); (%28(%r11), %)]
      call fibonacci
      movq %16any, %20(%rax)
      movq %31any, %3any
      addq %30(reuse=%31), %31any, %16any
      movq %29any, %30(reuse=%31)
      jmp label1(%29any)
    |}];
  let cfg =
    regalloc_helper
      ~args:(RegSet.of_list (reg_ops srcs))
      (module Loop)
      state cfg
    @@ fun state ->
    Format.printf "%a\n" (pp_preferences state.regs) state.preferences;
    [%expect
      {|
    [0 -> [rax: -1.000000, rbx: -1.000000, rcx: -1.000000, rdx: -1.000000, rsi: -1.000000, rdi: 0.000000, rsp: -1.000000, rbp: -1.000000, r8: -1.000000, r9: -1.000000, r10: -1.000000, r11: -1.000000, r12: -1.000000, r13: -1.000000, r14: -1.000000, r15: -1.000000], 1 ->
    [rax: -0.088000, rbx: 0.000000, rcx: -0.044000, rdx: -0.044000, rsi: -0.044000, rdi: -0.088000, rsp: 0.000000, rbp: 0.000000, r8: -0.044000, r9: -0.044000, r10: -0.044000, r11: -0.044000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 2 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 3 ->
    [rax: -0.088000, rbx: 0.000000, rcx: -0.044000, rdx: -0.044000, rsi: -0.044000, rdi: -0.088000, rsp: 0.000000, rbp: 0.000000, r8: -0.044000, r9: -0.044000, r10: -0.044000, r11: -0.044000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 4 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 5 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 6 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 7 ->
    [rax: 0.000000, rbx: -0.440000, rcx: -0.484000, rdx: -0.484000, rsi: -0.484000, rdi: -0.528000, rsp: -0.440000, rbp: -0.440000, r8: -0.484000, r9: -0.484000, r10: -0.484000, r11: -0.484000, r12: -0.440000, r13: -0.440000, r14: -0.440000, r15: -0.440000], 8 ->
    [rax: -0.220000, rbx: -0.220000, rcx: 0.000000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 9 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: 0.000000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 10 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: 0.000000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 11 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 12 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: 0.000000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 13 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: 0.000000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 14 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: 0.000000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 15 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: 0.000000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 16 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 17 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 18 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 19 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 20 ->
    [rax: 0.000000, rbx: -0.440000, rcx: -0.484000, rdx: -0.484000, rsi: -0.484000, rdi: -0.528000, rsp: -0.440000, rbp: -0.440000, r8: -0.484000, r9: -0.484000, r10: -0.484000, r11: -0.484000, r12: -0.440000, r13: -0.440000, r14: -0.440000, r15: -0.440000], 21 ->
    [rax: -0.220000, rbx: -0.220000, rcx: 0.000000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 22 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: 0.000000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 23 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: 0.000000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 24 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 25 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: 0.000000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 26 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: 0.000000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 27 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: 0.000000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 28 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: -0.220000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: 0.000000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 29 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 30 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 31 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 32 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 33 ->
    [rax: 0.000000, rbx: -2.000000, rcx: -2.000000, rdx: -2.000000, rsi: -2.000000, rdi: -2.000000, rsp: -2.000000, rbp: -2.000000, r8: -2.000000, r9: -2.000000, r10: -2.000000, r11: -2.000000, r12: -2.000000, r13: -2.000000, r14: -2.000000, r15: -2.000000]]
    |}];
    let rec reg =
      X86.Target.Virtual
        { id = 8; reg_class = Int; reg; reg_constr = UsePhysical X86.Regs.rcx }
    in
    let label = X86.Cfg.(block_label (zip (fst (X86.Cfg.focus 3 cfg)))) in
    Format.printf "Label: %a\n" (Format.pp_print_option X86.Cfg.pp_label) label;
    let dies = state.liveness.dies 3 reg in
    Format.printf "8(rcx) dies at: %a\n"
      Format.(pp_print_option pp_print_int)
      dies;
    [%expect {|
    Label: (3, "label3")
    8(rcx) dies at: 2
    |}]
  in
  Format.printf "%a" X86.Printer.pp_graph cfg;
  [%expect
    {|
      pcopy [(%rbx(1), %rdi(0))]
      jle label2, label3, %rbx(1), $1
    label1(local=false)(rax(32)):
      movq %rax(33), %rax(32)
      ret %rax(33)
    label2(local=false)():
      movq %rax(2), %rbx(1)
      jmp label1(%rax(2))
    label3(local=false)():
      movq %rax(5), %rbx(1)
      subq %rax(4), %rax(5), $1
      pcopy [(%rdi(6), %rax(4)); (%rax(7), %); (%rcx(8), %); (%rdx(9), %);
              (%rsi(10), %); (%rdi(11), %); (%r8(12), %); (%r9(13), %);
              (%r10(14), %); (%r11(15), %)]
      call fibonacci
      movq %r13(3), %rax(7)
      movq %rax(18), %rbx(1)
      subq %rax(17), %rax(18), $2
      pcopy [(%rdi(19), %rax(17)); (%rax(20), %); (%rcx(21), %); (%rdx(22), %);
              (%rsi(23), %); (%rdi(24), %); (%r8(25), %); (%r9(26), %);
              (%r10(27), %); (%r11(28), %)]
      call fibonacci
      movq %rax(16), %rax(20)
      movq %rbx(31), %r13(3)
      addq %rbx(30), %rbx(31), %rax(16)
      movq %rax(29), %rbx(30)
      jmp label1(%rax(29))
    |}]
