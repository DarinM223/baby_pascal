module RegSet = X86.Target.RegSet
module RegMap = X86.Target.RegMap

let get_vreg vreg =
  match vreg with
  | X86.Target.Virtual vreg -> vreg
  | r ->
    failwith @@ Format.asprintf "Not a virtual register, %a" X86.Target.pp_reg r

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
  preferences : float array array;
  mutable reg_current_var : X86.Target.virtual_reg option array;
  (* initially 0 *)
  mutable reg_current_pref : float array;
  mutable occupied : CCBV.t;
  saved_reg_current_var : X86.Target.virtual_reg option array array;
  saved_reg_current_pref : float array array;
  saved_occupied : CCBV.t array;
  liveness : Spill.X86.Liveness.t;
  dom :
    (module Dominator.S
       with type label = X86.Cfg.label
        and type uid = X86.Cfg.uid
        and type position = int);
}

let pp_preferences regs fmt preferences =
  let open Format in
  pp_open_box fmt 0;
  pp_print_string fmt "[";
  for i = 0 to Array.length preferences - 1 do
    pp_print_int fmt i;
    pp_print_string fmt " -> ";
    pp_open_box fmt 0;
    pp_print_string fmt "[";
    for j = 0 to Array.length preferences.(i) - 1 do
      let reg = regs.(j) in
      let pref = preferences.(i).(j) in
      fprintf fmt "%a: %f" X86.Target.pp_reg reg pref;
      if j <> Array.length preferences.(i) - 1 then pp_print_string fmt ", "
    done;
    pp_print_string fmt "]";
    pp_close_box fmt ();
    if i <> Array.length preferences - 1 then pp_print_string fmt ", "
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

let load_block_state ?(copy = false) state pos =
  let copy_arr = if copy then Array.copy else fun a -> a in
  let copy_bits = if copy then CCBV.copy else fun a -> a in
  state.reg_current_var <- copy_arr state.saved_reg_current_var.(pos);
  state.reg_current_pref <- copy_arr state.saved_reg_current_pref.(pos);
  state.occupied <- copy_bits state.saved_occupied.(pos);
  for reg = 0 to Array.length state.reg_current_var - 1 do
    match state.reg_current_var.(reg) with
    | Some vreg when not (X86.Target.equal_reg vreg.reg state.regs.(reg)) ->
      vreg.reg <- state.regs.(reg)
    | _ -> ()
  done

let store_block_state state pos =
  state.saved_reg_current_var.(pos) <- state.reg_current_var;
  state.saved_reg_current_pref.(pos) <- state.reg_current_pref;
  state.saved_occupied.(pos) <- state.occupied

exception NotColoredYet

let get_block_reg state pos vreg =
  let exception Return of int in
  try
    for reg = 0 to Array.length state.saved_reg_current_var.(pos) - 1 do
      match state.saved_reg_current_var.(pos).(reg) with
      | Some vreg' when X86.Target.equal_reg vreg (Virtual vreg') ->
        raise (Return reg)
      | _ -> ()
    done;
    raise NotColoredYet
  with Return reg -> reg

let get_register ?(don't_use_for_optimistic_moves = CCBV.empty ()) state uid var
    head : int * float * X86.Cfg.head =
  (* give preference bonus to ReuseOperand contraints *)
  begin match var with
  | X86.Target.Virtual { reg_constr = ReuseOperand (Virtual r); _ } ->
    let weight = state.block_execution_frequency uid in
    let reg_index = find_reg_index state.regs r.reg in
    state.preferences.(X86.Target.index var).(reg_index) <-
      state.preferences.(X86.Target.index var).(reg_index)
      +. (weight *. Weights.aff_should_be_same)
  | _ -> ()
  end;
  let preferences =
    state.preferences.(X86.Target.index var)
    |> Array.mapi (fun i pref -> (i, pref))
  in
  Logs.debug (fun m ->
      m "Preferences for %a are: %a\n" X86.Target.pp_reg var
        (pp_preferences state.regs)
        [| Array.map snd preferences |]);
  Logs.debug (fun m ->
      m "Occupied: %a\n"
        (Format.pp_print_list
           ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           X86.Target.pp_reg)
        (List.map (fun r -> state.regs.(r)) (CCBV.to_list state.occupied)));
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
        Array.mapi (fun i pref -> (i, pref)) state.preferences.(ovar.id)
      in
      Array.sort
        (fun (_, pref1) (_, pref2) -> Float.compare pref1 pref2)
        preferences;
      try
        for i = Array.length preferences - 1 downto 0 do
          let oreg, opref = preferences.(i) in
          if
            (not (CCBV.get state.occupied oreg))
            && not (CCBV.get don't_use_for_optimistic_moves oreg)
          then raise (Break (oreg, opref -. state.reg_current_pref.(oreg)))
        done
      with Break (oreg, other_win) ->
        if i + 1 < Array.length preferences then
          let _, next_pref = preferences.(i + 1) in
          let win = next_pref -. pref in
          if win +. other_win > state.block_execution_frequency uid then begin
            Logs.debug (fun m ->
                m "Adding move from %a to %a" X86.Target.pp_reg state.regs.(reg)
                  X86.Target.pp_reg state.regs.(oreg));
            (* modify occupied, reg_current_var and reg_current_pref for optimistic move *)
            ovar.reg <- state.regs.(oreg);
            CCBV.set state.occupied oreg;
            CCBV.reset state.occupied reg;
            state.reg_current_var.(oreg) <- Some ovar;
            state.reg_current_var.(reg) <- None;
            state.reg_current_pref.(oreg) <- next_pref;
            state.reg_current_pref.(reg) <- 0.;
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

let swap_regs state src dest =
  begin match state.reg_current_var.(src) with
  | Some src_vreg -> src_vreg.reg <- state.regs.(dest)
  | _ -> ()
  end;
  begin match state.reg_current_var.(dest) with
  | Some dest_vreg -> dest_vreg.reg <- state.regs.(src)
  | _ -> ()
  end;
  let tmp = CCBV.get state.occupied src in
  CCBV.set_bool state.occupied src (CCBV.get state.occupied dest);
  CCBV.set_bool state.occupied dest tmp;
  let tmp = state.reg_current_var.(src) in
  state.reg_current_var.(src) <- state.reg_current_var.(dest);
  state.reg_current_var.(dest) <- tmp;
  let tmp = state.reg_current_pref.(src) in
  state.reg_current_pref.(src) <- state.reg_current_pref.(dest);
  state.reg_current_pref.(dest) <- tmp

let permute_values state (permutation : int array) (head : X86.Cfg.head) =
  Logs.debug (fun m ->
      m "Permute values permutation %s occupied: %a\n"
        ([%show: int array] permutation)
        (Format.pp_print_list
           ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
           X86.Target.pp_reg)
        (List.map (fun r -> state.regs.(r)) (CCBV.to_list state.occupied)));
  let num_regs = Array.length state.regs in
  let num_used = Array.make num_regs 0 in
  for r = 0 to num_regs - 1 do
    let old_reg = permutation.(r) in
    (* todo: phi jump args are killed at end of block,
       once that is fixed, then restore the commented code *)
    (* if CCBV.get state.occupied old_reg then *)
    num_used.(old_reg) <- num_used.(old_reg) + 1
    (* else permutation.(r) <- r (* source register is not live, do nothing *) *)
  done;
  let r = ref 0 in
  let srcs = CCVector.create () in
  let dests = CCVector.create () in
  (* create initial parallel copy *)
  while !r < num_regs do
    let old_reg = permutation.(!r) in
    (* copy isn't possible if destination register is still used *)
    if old_reg = !r || num_used.(!r) > 0 then incr r
    else begin
      begin match state.reg_current_var.(old_reg) with
      | Some vreg -> vreg.reg <- state.regs.(!r)
      | _ -> ()
      end;
      CCBV.set state.occupied !r;
      CCBV.reset state.occupied old_reg;
      state.reg_current_var.(!r) <- state.reg_current_var.(old_reg);
      state.reg_current_var.(old_reg) <- None;
      state.reg_current_pref.(!r) <- state.reg_current_pref.(old_reg);
      state.reg_current_pref.(old_reg) <- 0.;
      CCVector.push srcs (X86.Target.Reg state.regs.(old_reg));
      CCVector.push dests (X86.Target.Reg state.regs.(!r));
      permutation.(!r) <- !r;
      num_used.(old_reg) <- num_used.(old_reg) - 1;
      if old_reg < !r && num_used.(old_reg) = 0 then r := old_reg else incr r
    end
  done;
  let head =
    if CCVector.length dests > 0 then
      X86.Cfg.Head
        ( head,
          Instruction
            (X86.Target.pcopy ~dests:(CCVector.to_list dests)
               ~srcs:(CCVector.to_list srcs)) )
    else head
  in
  (* resolve remaining cycles with permutation instructions *)
  r := 0;
  let head = ref head in
  while !r < num_regs do
    let old_reg = permutation.(!r) in
    if old_reg = !r then incr r
    else begin
      let r' = permutation.(old_reg) in
      swap_regs state old_reg r';
      Logs.debug (fun m ->
          m "Swapping %a with %a\n" X86.Target.pp_reg state.regs.(old_reg)
            X86.Target.pp_reg state.regs.(r'));
      head :=
        X86.Cfg.Head
          ( !head,
            Instruction
              (X86.Target.pcopy
                 ~dests:[ Reg state.regs.(r'); Reg state.regs.(old_reg) ]
                 ~srcs:[ Reg state.regs.(old_reg); Reg state.regs.(r') ]) );
      permutation.(old_reg) <- old_reg;
      permutation.(!r) <- r'
    end
  done;
  !head

module type EnforceConstraints = sig
  val dest_mapping : X86.Target.reg array
  (** Mapping from register to destination register in original instruction.
      Used for reusing existing virtual registers in the original pcopy. *)

  val clobber_mapping : X86.Target.reg array
  (** Mapping from register to constrained virtual register that clobbers the
      register. *)

  val live_through_regs : CCBV.t
  (** Registers that are currently being occupied by values that live through
      the instruction occupied regs - regs that die at the instruction *)

  val constrained_def_regs : CCBV.t
  (** Registers that are constrained in parallel copy definitions without a
      corresponding use. These registers will be clobbered after the
      instruction, similarly to caller-save registers after a call. *)

  val need_reassignment : bool
  (** True if a parallel copy shuffling the registers to fit the constraints is
      necessary *)
end

let enforce_constraints_state state uid instr_num instr =
  let num_regs = Array.length state.regs in
  (* Mapping from register to destination register in original instruction.
     Used for reusing existing virtual registers in the original pcopy. *)
  let dest_mapping = Array.make num_regs X86.Target.Tombstone in
  let clobber_mapping = Array.make num_regs X86.Target.Tombstone in
  (* Registers that are currently being occupied by values
     that live through the instruction
     occupied regs - regs that die at the instruction *)
  let live_through_regs = CCBV.copy state.occupied in
  let constrained_def_regs = CCBV.create ~size:num_regs false in
  let need_reassignment = ref false in
  let remove_constrained_use_live_throughs = function
    | (X86.Target.Virtual a' as a), _ when dies state uid a instr_num ->
      let reg = find_reg_index state.regs a'.reg in
      Logs.debug (fun m ->
          m "Removing %a from live throughs\n" X86.Target.pp_reg
            state.regs.(reg));
      CCBV.reset live_through_regs reg
    | _ -> ()
  in
  let mark_constrained_def_regs f = function
    | ( X86.Target.Virtual { reg_constr = UsePhysical phys; _ }
      | X86.Target.Physical phys ) as r ->
      begin try
        let reg_index = find_reg_index state.regs (Physical phys) in
        Logs.debug (fun m ->
            m "Setting %a as constrained def\n" X86.Target.pp_reg
              state.regs.(reg_index));
        CCBV.set constrained_def_regs reg_index;
        f reg_index r;
        if CCBV.get live_through_regs reg_index then need_reassignment := true
      with _ -> ()
      end
    | _ -> ()
  in
  let rec go_uses_defs = function
    | X86.Target.Reg use :: uses, X86.Target.Reg def :: defs ->
      if use <> Tombstone && def <> Tombstone then begin
        remove_constrained_use_live_throughs (use, def);
        mark_constrained_def_regs (fun idx r -> dest_mapping.(idx) <- r) def
      end;
      go_uses_defs (uses, defs)
    | _ :: uses, _ :: defs -> go_uses_defs (uses, defs)
    | [], X86.Target.Reg def :: defs ->
      if def <> Tombstone then begin
        mark_constrained_def_regs (fun idx r -> clobber_mapping.(idx) <- r) def
      end;
      go_uses_defs ([], defs)
    | _ -> ()
  in
  go_uses_defs (instr.X86.Target.uses, instr.defs);
  CCBV.iter_true live_through_regs (fun reg ->
      Logs.debug (fun m ->
          m "Live through: %a\n" X86.Target.pp_reg state.regs.(reg)));
  let module EnforceConstraints = struct
    let dest_mapping = dest_mapping
    let clobber_mapping = clobber_mapping
    let live_through_regs = live_through_regs
    let constrained_def_regs = constrained_def_regs
    let need_reassignment = !need_reassignment
  end in
  (module EnforceConstraints : EnforceConstraints)

(** Unlike in the normal preference based register allocation algorithm, enforce
    constraints are only enforced on parallel copies. Constrained uses are uses
    in the pcopy that have a corresponding def, constrained defs are definitions
    at the end which don't have a corresponding use. *)
let enforce_constraints_assignment (module State : EnforceConstraints) state
    instr =
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
            m "No edge from %a to %a because it clobbers live through"
              X86.Target.pp_reg state.regs.(r) X86.Target.pp_reg state.regs.(l))
      else if
        (* Don't move a live through value that currently occupies a
             constrained def register into another constrained def register
             That register will be clobbered and won't live through the instruction *)
        CCBV.get constrained_def_regs l
        && CCBV.get live_through_regs r
        && CCBV.get constrained_def_regs r
      then
        Logs.debug (fun m ->
            m "No edge from %a to %a because it will be clobbered"
              X86.Target.pp_reg state.regs.(r) X86.Target.pp_reg state.regs.(l))
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
  permutation

let enforce_constraints_pcopy (module State : EnforceConstraints) state uid
    instr_num permutation =
  let num_regs = Array.length state.regs in
  let open State in
  (* After, the index of permutation is the destination register
     and the value is the source register *)
  let srcs = ref [] in
  let dests = ref [] in
  let saved_pref = Array.make num_regs 0. in
  let kill_reg = Array.make num_regs false in
  for dest = 0 to num_regs - 1 do
    let old_reg = permutation.(dest) in
    saved_pref.(dest) <- state.reg_current_pref.(old_reg);
    match state.reg_current_var.(old_reg) with
    | Some src when old_reg <> dest ->
      (* If register is live-through and it isn't a
           constrained definition register, then it will still be accessible
           after this instruction, so don't modify the assigned register. *)
      if
        let src_reg = find_reg_index state.regs src.reg in
        CCBV.get live_through_regs src_reg
        && not (CCBV.get constrained_def_regs src_reg)
      then
        Logs.debug (fun m ->
            m
              "Not killing register %a because its register is live-through \
               and not a constrained definition"
              X86.Target.pp_reg (Virtual src))
      else begin
        src.reg <- state.regs.(dest);
        kill_reg.(old_reg) <- true
      end;
      if old_reg <> dest || dest_mapping.(dest) <> Tombstone then begin
        srcs := X86.Target.Reg state.regs.(old_reg) :: !srcs;
        dests := X86.Target.Reg state.regs.(dest) :: !dests
      end;
      dest_mapping.(dest) <-
        begin match dest_mapping.(dest) with
        | Tombstone -> Virtual src
        | r -> r
        end
    | _ -> ()
  done;
  for dest = 0 to num_regs - 1 do
    if kill_reg.(dest) then begin
      Logs.debug (fun m ->
          m "Killing register %a for %a\n" X86.Target.pp_reg state.regs.(dest)
            X86.Target.pp_reg dest_mapping.(dest));
      state.reg_current_var.(dest) <- None;
      state.reg_current_pref.(dest) <- 0.;
      CCBV.reset state.occupied dest
    end;
    begin match dest_mapping.(dest) with
    | Virtual vreg ->
      Logs.debug (fun m ->
          m "Setting register for %a to %a\n" X86.Target.pp_reg (Virtual vreg)
            X86.Target.pp_reg state.regs.(dest));
      vreg.reg <- state.regs.(dest);
      if not (dies state uid (Virtual vreg) instr_num) then begin
        Logs.debug (fun m ->
            m "Setting as occupied: %a\n" X86.Target.pp_reg state.regs.(dest));
        state.reg_current_var.(dest) <- Some vreg;
        state.reg_current_pref.(dest) <- saved_pref.(dest);
        CCBV.set state.occupied dest
      end
      else begin
        Logs.debug (fun m ->
            m "Killing occupied: %a\n" X86.Target.pp_reg state.regs.(dest));
        state.reg_current_var.(dest) <- None;
        state.reg_current_pref.(dest) <- 0.;
        CCBV.reset state.occupied dest
      end
    | _ -> ()
    end
  done;
  for dest = 0 to num_regs - 1 do
    match clobber_mapping.(dest) with
    | Virtual vreg when not (dies state uid (Virtual vreg) instr_num) ->
      vreg.reg <- state.regs.(dest);
      Logs.debug (fun m ->
          m "Live through clobbering register: %a\n" X86.Target.pp_reg
            state.regs.(dest));
      state.reg_current_var.(dest) <- Some vreg;
      state.reg_current_pref.(dest) <- saved_pref.(dest);
      CCBV.set state.occupied dest
    | _ -> ()
  done;
  Logs.debug (fun m ->
      m "Shuffling Dests: %a Srcs: %a\n" X86.Target.pp_operands !dests
        X86.Target.pp_operands !srcs);
  X86.Target.pcopy ~dests:!dests ~srcs:!srcs

let enforce_constraints state uid instr_num pcopy head =
  let s = enforce_constraints_state state uid instr_num pcopy in
  let module State = (val s) in
  let need_swap =
    CCBV.(inter State.live_through_regs State.constrained_def_regs)
  in
  if not State.need_reassignment then begin
    let orig_pcopy = pcopy in
    let assignment = Array.init (Array.length state.regs) (fun r -> r) in
    let extra_srcs = ref [] in
    let extra_dests = ref [] in
    let rec set_use_def = function
      | ( X86.Target.Reg (Virtual use) :: uses,
          X86.Target.Reg (Virtual { reg_constr = UsePhysical phys; _ }) :: defs
        ) ->
        let def = find_reg_index state.regs (Physical phys) in
        let use = find_reg_index state.regs use.reg in
        assignment.(def) <- use;
        set_use_def (uses, defs)
      | use :: uses, def :: defs ->
        (* Some pcopies don't have register constrained definitions, add those directly *)
        extra_srcs := use :: !extra_srcs;
        extra_dests := def :: !extra_dests;
        set_use_def (uses, defs)
      | _ -> ()
    in
    set_use_def (pcopy.uses, pcopy.defs);
    Logs.debug (fun m ->
        m "Dest Mapping %s\n" ([%show: X86.Target.reg array] State.dest_mapping));
    Logs.debug (fun m ->
        m "Assignments %s\n"
          ([%show: X86.Target.reg array]
             (Array.map (fun r -> state.regs.(r)) assignment)));
    let pcopy =
      enforce_constraints_pcopy (module State) state uid instr_num assignment
    in
    let pcopy =
      {
        pcopy with
        uses = List.rev !extra_srcs @ pcopy.uses;
        defs = List.rev !extra_dests @ pcopy.defs;
      }
    in
    Logs.debug (fun m ->
        m "Regular PCopy %a created from %a\n" X86.Target.pp_instr pcopy
          X86.Target.pp_instr orig_pcopy);
    (head, pcopy)
  end
  else if not (CCBV.is_empty need_swap) then begin
    Logs.debug (fun m ->
        m "Need swap: %s\n"
          ([%show: X86.Target.reg list]
             (List.map (fun r -> state.regs.(r)) (CCBV.to_list need_swap))));
    (* swap with not constrained def - live throughs *)
    let free_non_constrained =
      CCBV.(diff (negate State.constrained_def_regs) State.live_through_regs)
    in
    let rec go srcs dests = function
      | src :: need_swap, dest :: free_non_constrained ->
        CCBV.reset State.live_through_regs src;
        CCBV.set State.live_through_regs dest;
        swap_regs state src dest;
        go
          (X86.Target.Reg state.regs.(src) :: Reg state.regs.(dest) :: srcs)
          (X86.Target.Reg state.regs.(dest) :: Reg state.regs.(src) :: dests)
          (need_swap, free_non_constrained)
      | _ -> (srcs, dests)
    in
    let srcs, dests =
      go [] [] (CCBV.to_list need_swap, CCBV.to_list free_non_constrained)
    in
    let pcopy' = X86.Target.pcopy ~dests ~srcs in
    Logs.debug (fun m ->
        m "Emitting swap parallel copy: %a\n" X86.Target.pp_instr pcopy');
    let assignment =
      enforce_constraints_assignment (module State) state pcopy
    in
    let pcopy =
      enforce_constraints_pcopy (module State) state uid instr_num assignment
    in
    (X86.Cfg.Head (head, Instruction pcopy'), pcopy)
  end
  else
    let assignment = enforce_constraints_assignment s state pcopy in
    let pcopy = enforce_constraints_pcopy s state uid instr_num assignment in
    (head, pcopy)

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
  let permutations = Array.init (Array.length state.regs) (fun r -> r) in
  let args =
    let open X86.Target in
    List.fold_right
      (fun (arg, phi) args ->
        match (arg, phi) with
        | ( Reg (Virtual { reg = arg_reg; _ } | (Physical _ as arg_reg)),
            (Virtual { reg = Physical phi_reg; _ } | Physical phi_reg) ) ->
          let arg_reg_idx = find_reg_index state.regs arg_reg in
          let phi_reg_idx = find_reg_index state.regs (Physical phi_reg) in
          if arg_reg_idx <> phi_reg_idx then begin
            Logs.debug (fun m ->
                m "Setting jump reg %a to phi reg %a\n" X86.Target.pp_reg
                  state.regs.(arg_reg_idx) X86.Target.pp_reg
                  state.regs.(phi_reg_idx));
            permutations.(phi_reg_idx) <- arg_reg_idx;
            (* if phi is occupied, swap it with arg_reg *)
            (* todo: check if correct *)
            if CCBV.get state.occupied phi_reg_idx then begin
              permutations.(arg_reg_idx) <- phi_reg_idx
            end;
            Reg (Physical phi_reg) :: args
          end
          else arg :: args
        | _ -> arg :: args)
      (List.combine args phis) []
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
  let head = permute_values state permutations head in
  X86.Cfg.unfocus ((head, Last last), cfg)

let color_instruction state uid instr_num head instr =
  let head, instr =
    if instr.X86.Target.instr = "pcopy" then
      enforce_constraints state uid instr_num instr head
    else (head, instr)
  in
  (* Gather reuse operands *)
  let reuse_operands, _ =
    X86.Target.fold_reg_defs
      (fun acc -> function
        | X86.Target.Virtual { reg_constr = ReuseOperand reg; _ } as r ->
          (RegMap.add reg r acc, r)
        | r -> (acc, r))
      RegMap.empty instr
  in
  (* Make sure that killed use registers aren't used for optimistic moves,
     because the move would be inserted before the register is killed *)
  let don't_use_for_optimistic_moves =
    CCBV.create ~size:(Array.length state.regs) false
  in
  let remove_reuse_reg reg reg' =
    if RegMap.mem reg reuse_operands then begin
      Logs.debug (fun m ->
          m "Reused virtual register %a with physical register %a"
            X86.Target.pp_reg reg X86.Target.pp_reg reg');
      X86.Target.Tombstone
    end
    else reg'
  in
  (* Update instruction uses, replacing virtual registers with physical registers,
       removing dead uses from the currently occupied registers,
       and removing reuse operand uses *)
  let instr =
    X86.Target.map_reg_uses
      (fun reg ->
        match reg with
        | X86.Target.Virtual a' as a when dies state uid a instr_num ->
          Logs.debug (fun m ->
              m "Killing dead register %a for %a\n" X86.Target.pp_reg a'.reg
                X86.Target.pp_reg a);
          let reg = find_reg_index state.regs a'.reg in
          CCBV.set don't_use_for_optimistic_moves reg;
          state.reg_current_var.(reg) <- None;
          state.reg_current_pref.(reg) <- 0.;
          CCBV.reset state.occupied reg;
          remove_reuse_reg a a'.reg
        | X86.Target.Virtual a' ->
          Logs.debug (fun m ->
              m "Setting existing colored register %a as %a\n" X86.Target.pp_reg
                reg X86.Target.pp_reg a'.reg);
          remove_reuse_reg reg a'.reg
        | r -> remove_reuse_reg r r)
      instr
  in
  (* Assign registers for definitions *)
  let head, instr =
    X86.Target.fold_reg_defs
      (fun head -> function
        | X86.Target.Virtual r' as r when X86.Target.equal_reg r'.reg r ->
          let reg, pref, head =
            get_register ~don't_use_for_optimistic_moves state uid r head
          in
          Logs.debug (fun m ->
              m "Setting register for %a to %a\n" X86.Target.pp_reg (Virtual r')
                X86.Target.pp_reg state.regs.(reg));
          r'.reg <- state.regs.(reg);
          if not (dies state uid r instr_num) then begin
            CCBV.set state.occupied reg;
            state.reg_current_var.(reg) <- Some r';
            state.reg_current_pref.(reg) <- pref
          end;
          (head, r'.reg)
        | r -> (head, r))
      head instr
  in
  (* Check reuse operands assigned registers match *)
  RegMap.iter
    (fun use def ->
      match (use, def) with
      | X86.Target.Virtual use, X86.Target.Virtual def
        when X86.Target.equal_reg use.reg def.reg ->
        ()
      | _ ->
        failwith
        @@ Format.asprintf "Invalid matching: %a with %a" X86.Target.pp_reg use
             X86.Target.pp_reg def)
    reuse_operands;
  (head, instr)

let color_block state ((first, tail) as block : X86.Cfg.block) : X86.Cfg.block =
  let uid = X86.Cfg.id block in
  let head =
    match first with
    | X86.Cfg.Entry -> X86.Cfg.First first
    | X86.Cfg.Label (l, info) ->
      let head, args =
        List.fold_left_map
          (fun head -> function
            | X86.Target.Virtual phi' as phi
              when X86.Target.equal_reg phi'.reg phi ->
              let reg, pref, head = get_register state uid phi head in
              Logs.debug (fun m ->
                  m "Setting register for %a to %a\n" X86.Target.pp_reg
                    (Virtual phi') X86.Target.pp_reg state.regs.(reg));
              phi'.reg <- state.regs.(reg);
              state.reg_current_var.(reg) <- Some phi';
              state.reg_current_pref.(reg) <- pref;
              CCBV.set state.occupied reg;
              (head, phi'.reg)
            | r -> (head, r))
          (X86.Cfg.First first) info.args
      in
      let rec replace_first first = function
        | X86.Cfg.First _ -> X86.Cfg.First first
        | Head (head, mid) -> Head (replace_first first head, mid)
      in
      replace_first (X86.Cfg.Label (l, { info with args })) head
  in
  let rec go instr_num head = function
    | X86.Cfg.Tail (Instruction instr, tail) ->
      let head, instr = color_instruction state uid instr_num head instr in
      go (instr_num + 1) (X86.Cfg.Head (head, Instruction instr)) tail
    | X86.Cfg.Last l ->
      (* todo: propagate branch args to the affinity chunk *)
      begin match l with
      | X86.Printer.Exit -> (head, X86.Cfg.Last l)
      | X86.Printer.Branch (i, lab) ->
        let head, i = color_instruction state uid instr_num head i in
        (head, X86.Cfg.Last (Branch (i, lab)))
      | X86.Printer.CBranch (i, lab1, lab2) ->
        let head, i = color_instruction state uid instr_num head i in
        (head, X86.Cfg.Last (CBranch (i, lab1, lab2)))
      | X86.Printer.Return i ->
        let head, i = color_instruction state uid instr_num head i in
        (head, X86.Cfg.Last (Return i))
      end
  in
  let block = X86.Cfg.zip (go 0 head tail) in
  let module Dom = (val state.dom) in
  let pos = Dom.position_of_uid uid in
  state.processed.(pos) <- true;
  block

let after_color_block state (cfg : X86.Cfg.graph) pos : X86.Cfg.graph =
  let module Dom = (val state.dom) in
  store_block_state state pos;
  let cfg =
    List.fold_left
      (fun cfg pred ->
        if state.processed.(pred) then begin
          load_block_state state pred;
          implement_phi_copies state cfg ~src:pred ~dest:pos
        end
        else cfg)
      cfg (Dom.predecessors pos)
  in
  load_block_state state pos;
  let succs = Dom.successors pos in
  (* if block only has one successor we can add phi copies for current block *)
  match succs with
  | [ succ ] ->
    if state.processed.(succ) then
      implement_phi_copies state cfg ~src:pos ~dest:succ
    else cfg
  | _ -> cfg

let build_preferences state graph : unit =
  let preferences = state.preferences in
  let rec handle_operand ?(def = false) uid live = function
    | X86.Target.(Reg (Virtual { id; reg_constr = ReuseOperand reg; _ }))
      when def ->
      (* add preferences to use variable when there is a reuse operand def *)
      let op = X86.Target.index reg in
      for i = 0 to Array.length preferences.(op) - 1 do
        preferences.(op).(i) <- preferences.(op).(i) +. preferences.(id).(i)
      done
    | X86.Target.(Reg (Virtual { id; reg_constr = UsePhysical phys; _ })) ->
      begin try
        let reg = find_reg_index state.regs (X86.Target.Physical phys) in
        let weight = state.block_execution_frequency uid in
        let penalty =
          weight *. if def then Weights.def_factor else Weights.use_factor
        in
        (* give penalties to all registers that are not the constrained register. *)
        for i = 0 to Array.length preferences.(id) - 1 do
          if i <> reg then
            preferences.(id).(i) <- preferences.(id).(i) -. penalty
        done;
        let penalty = penalty *. Weights.neighbor_factor in
        (* give penalties to all other live variables for the constrained register *)
        CCBV.iter_true live (fun live ->
            if live <> id then
              preferences.(live).(reg) <- preferences.(live).(reg) -. penalty)
      with _ -> ()
      end
    | X86.Target.Label (_, ops) -> List.iter (handle_operand uid live) ops
    | _ -> ()
  in
  let rec handle_pcopy = function
    | ( X86.Target.Reg (Virtual { id = src; _ }) :: srcs,
        X86.Target.Reg (Virtual { id = dest; reg_constr = UsePhysical _; _ })
        :: dests ) ->
      (* add preferences to use variable when there is a pcopy to a constrained def *)
      for i = 0 to Array.length preferences.(src) - 1 do
        preferences.(src).(i) <- preferences.(src).(i) +. preferences.(dest).(i)
      done;
      handle_pcopy (srcs, dests)
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
    CCBV.union_into ~into:live uses;
    if instr.instr = "pcopy" then handle_pcopy (instr.uses, instr.defs)
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
      let merged = state.preferences.(Unionfind.to_int merged_repr) in
      let other = state.preferences.(Unionfind.to_int other_repr) in
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
    Array.blit state.preferences.(v_repr) 0 state.preferences.(v) 0
      (Array.length state.preferences.(v))

let combine_congruence_classes state graph =
  let classes = Unionfind.create state.num_vars in
  let rpo = X86.Cfg.reverse_postorder_dfs graph in
  List.iter (create_congruence_class state classes graph) rpo;
  Array.iteri
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
  let module NextUseDistances = Spill.X86.NextUseDistances (Loop) in
  let next_use_distances = NextUseDistances.calc cfg in
  let liveness = Spill.X86.Liveness.calc cfg in
  let module Spill' =
    Spill.X86.Make (Loop) (NextUseDistances)
      (struct
        let reg_class = X86.Target.Int
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
    occupied = CCBV.create ~size:(Array.length regs) false;
    saved_reg_current_var =
      Array.init Dom.size (fun _ -> Array.make (Array.length regs) None);
    saved_reg_current_pref =
      Array.init Dom.size (fun _ -> Array.make (Array.length regs) 0.);
    saved_occupied =
      Array.init Dom.size (fun _ -> CCBV.create ~size:(Array.length regs) false);
    processed = Array.make Dom.size false;
    num_vars;
    preferences = Array.make_matrix num_vars (Array.length regs) 0.;
  }

let create_phi state cfg pos v =
  let rec get_reg v' =
    match v' with
    | X86.Target.Virtual { reg; _ } when not (X86.Target.equal_reg reg v') ->
      reg
    | X86.Target.Physical _ -> v'
    | _ ->
      if not (X86.Target.equal_reg v v') then begin
        let default_reg = get_reg v in
        Logs.debug (fun m ->
            m "create_phi: uncolored register %a, using default %a\n"
              X86.Target.pp_reg v' X86.Target.pp_reg default_reg);
        default_reg
      end
      else
        failwith
        @@ Format.asprintf "create_phi: uncolored register %a" X86.Target.pp_reg
             v
  in
  let module Dom = (val state.dom) in
  let phi_block_label = Dom.label_of_position pos in
  (* add phi to block label at pos *)
  let (head, tail), cfg = X86.Cfg.focus (X86.Cfg.idd phi_block_label) cfg in
  let head =
    match head with
    | X86.Cfg.First (Label (l, info)) ->
      X86.Cfg.First (Label (l, { info with args = get_reg v :: info.args }))
    | X86.Cfg.First Entry ->
      failwith "create_phi: cannot create phi for entry block"
    | X86.Cfg.Head _ -> failwith "create_phi: expected first"
  in
  let cfg = X86.Cfg.unfocus ((head, tail), cfg) in
  (* go into every predecessor of the block and add the phi argument to the end of its jump *)
  let go_pred cfg pred =
    load_block_state state pred;
    let zblock, cfg = X86.Cfg.(focus (idd (Dom.label_of_position pred)) cfg) in
    let head, last = X86.Cfg.goto_end zblock in
    (* if predecessor is unprocessed, insert the uncolored virtual register,
       it will be colored with the right register later. *)
    let v = if state.processed.(pred) then get_reg v else v in
    let rewrite_edge instr =
      let add_phi_arg = function
        | X86.Target.Label (l, ops) when phi_block_label = Some l ->
          X86.Target.Label (l, Reg v :: ops)
        | op -> op
      in
      X86.Target.map_uses add_phi_arg instr
    in
    let last =
      match last with
      | Exit | Return _ -> last
      | Branch (instr, l) -> Branch (rewrite_edge instr, l)
      | CBranch (instr, l1, l2) -> CBranch (rewrite_edge instr, l1, l2)
    in
    X86.Cfg.unfocus ((head, Last last), cfg)
  in
  let cfg = List.fold_left go_pred cfg (Dom.predecessors pos) in
  load_block_state state pos;
  cfg

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
  let liveness = Spill.X86.Liveness.calc cfg in
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
    Logs.debug (fun m -> m "Coloring block %d:\n" uid);
    let preds = Loop.Dom.predecessors pos in
    if not @@ CCList.is_empty preds then begin
      load_block_state ~copy:true alloc_state (List.hd preds);
      store_block_state alloc_state pos
    end;
    load_block_state alloc_state pos;
    alloc_state.select_state.curr_block := uid;

    (* color initial arguments for entry block *)
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
    let cfg = X86.Cfg.(unfocus (zblock, cfg)) in

    Logs.debug (fun m ->
        m "Current vars: %s\n"
          ([%show: X86.Target.reg option list]
             (List.map
                (Option.map (fun v -> X86.Target.Virtual v))
                (Array.to_list alloc_state.reg_current_var))));

    (* for each live in, check if it is the same across predecessors
       if not, create a phi node *)
    let live_in = liveness.live_in pos in
    let set_live_in v cfg =
      try
        Logs.debug (fun m -> m "Live in: %a\n" X86.Target.pp_reg v);
        let assigned = get_block_reg alloc_state pos v in
        let pred_needs_to_create_phi pred =
          if not alloc_state.processed.(pred) then
            (* always create phi for backedge *)
            true
          else begin
            Logs.debug (fun m ->
                m "Checking pred %d for block %d\n"
                  (X86.Cfg.idd (Loop.Dom.label_of_position pred))
                  uid);
            (not (CCBV.get alloc_state.saved_occupied.(pred) assigned))
            || Option.map
                 (fun v -> v.X86.Target.id)
                 alloc_state.saved_reg_current_var.(pred).(assigned)
               <> Some (X86.Target.index v)
          end
        in
        if List.exists pred_needs_to_create_phi preds then begin
          Logs.debug (fun m ->
              m "Block %d needs to create phi for %a" uid X86.Target.pp_reg v);
          create_phi alloc_state cfg pos v
        end
        else cfg
      with NotColoredYet -> cfg
    in
    let cfg = X86.Target.RegSet.fold set_live_in live_in cfg in

    Logs.debug (fun m ->
        m "Block %d Occupied: %a\n" uid
          (Format.pp_print_list
             ~pp_sep:(fun fmt _ -> Format.fprintf fmt ", ")
             X86.Target.pp_reg)
          (List.map
             (fun r -> alloc_state.regs.(r))
             (CCBV.to_list alloc_state.occupied)));

    (* now color registers for all the instructions in block *)
    let zblock, cfg = X86.Cfg.focus uid cfg in
    let block = color_block alloc_state (X86.Cfg.zip zblock) in
    let cfg = X86.Cfg.(unfocus (unzip block, cfg)) in
    after_color_block alloc_state cfg pos
  in
  let blockorder = blockorder alloc_state in
  Logs.debug (fun m ->
      m "Block order: %s\n"
        ([%show: X86.Cfg.label option list]
           (List.map Loop.Dom.label_of_position blockorder)));
  List.fold_left go_block cfg blockorder

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
      movq %rax, $0
      jmp label6
    label1(local=false)():
      exit
    label2(local=false)(rbx):
      jl label3, label1, %rbx, $100
    label3(local=false)():
      movq %rsi, %rbx
      pcopy [(%r13, %rsi); (%rsi, %rbx)]
      jmp label4(%rsi, %r13)
    label4(local=false)(rsi, r13):
      jl label5, label2(%rsi), %r13, $100
    label5(local=false)():
      movq %r15, %rsi
      addq %r15, %, $1
      movq %r15, %r15
      movq %r14, %r13
      addq %r14, %, $1
      movq %r14, %r14
      pcopy [(%rsi, %r15); (%r15, %rsi)]
      pcopy [(%r13, %r14); (%r14, %r13)]
      jmp label4(%rsi, %r13)
    label6(local=false)():
      pcopy [(%rbx, %rax)]
      jmp label2(%rbx)
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
      pcopy [(%33(%rax), %32any)]
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
    [rax: 0.000000, rbx: -2.000000, rcx: -2.000000, rdx: -2.000000, rsi: -2.000000, rdi: -2.000000, rsp: -2.000000, rbp: -2.000000, r8: -2.000000, r9: -2.000000, r10: -2.000000, r11: -2.000000, r12: -2.000000, r13: -2.000000, r14: -2.000000, r15: -2.000000], 3 ->
    [rax: -0.088000, rbx: 0.000000, rcx: -0.044000, rdx: -0.044000, rsi: -0.044000, rdi: -0.088000, rsp: 0.000000, rbp: 0.000000, r8: -0.044000, r9: -0.044000, r10: -0.044000, r11: -0.044000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 4 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 5 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 6 ->
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
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 18 ->
    [rax: -0.220000, rbx: -0.220000, rcx: -0.220000, rdx: -0.220000, rsi: -0.220000, rdi: 0.000000, rsp: -0.220000, rbp: -0.220000, r8: -0.220000, r9: -0.220000, r10: -0.220000, r11: -0.220000, r12: -0.220000, r13: -0.220000, r14: -0.220000, r15: -0.220000], 19 ->
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
    [rax: 0.000000, rbx: -2.000000, rcx: -2.000000, rdx: -2.000000, rsi: -2.000000, rdi: -2.000000, rsp: -2.000000, rbp: -2.000000, r8: -2.000000, r9: -2.000000, r10: -2.000000, r11: -2.000000, r12: -2.000000, r13: -2.000000, r14: -2.000000, r15: -2.000000], 30 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 31 ->
    [rax: 0.000000, rbx: 0.000000, rcx: 0.000000, rdx: 0.000000, rsi: 0.000000, rdi: 0.000000, rsp: 0.000000, rbp: 0.000000, r8: 0.000000, r9: 0.000000, r10: 0.000000, r11: 0.000000, r12: 0.000000, r13: 0.000000, r14: 0.000000, r15: 0.000000], 32 ->
    [rax: 0.000000, rbx: -2.000000, rcx: -2.000000, rdx: -2.000000, rsi: -2.000000, rdi: -2.000000, rsp: -2.000000, rbp: -2.000000, r8: -2.000000, r9: -2.000000, r10: -2.000000, r11: -2.000000, r12: -2.000000, r13: -2.000000, r14: -2.000000, r15: -2.000000], 33 ->
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
      pcopy [(%rbx, %rdi)]
      jle label2, label3, %rbx, $1
    label1(local=false)(rax):
      pcopy []
      ret %rax
    label2(local=false)():
      movq %rax, %rbx
      jmp label1(%rax)
    label3(local=false)():
      movq %rax, %rbx
      subq %rax, %, $1
      pcopy [(%r15, %rdi); (%rdi, %r15)]
      pcopy [(%rdi, %rax)]
      call fibonacci
      movq %r13, %rax
      movq %rdi, %rbx
      subq %rdi, %, $2
      pcopy []
      call fibonacci
      movq %rax, %rax
      movq %rsi, %r13
      addq %rsi, %, %rax
      movq %rax, %rsi
      jmp label1(%rax)
    |}]
