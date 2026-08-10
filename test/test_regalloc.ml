open Alcotest
open Baby_pascal

type reg_mapping = (X86.Target.physical_reg * bool) list

let get_vreg vreg =
  match vreg with
  | X86.Target.Virtual vreg -> vreg
  | r ->
    failwith @@ Format.asprintf "Not a virtual register, %a" X86.Target.pp_reg r

let get_physical = function
  | X86.Target.Physical p -> p
  | r ->
    failwith
    @@ Format.asprintf "Not a physical register, %a" X86.Target.pp_reg r

let find_reg_index regs reg : int =
  match CCArray.find_idx (X86.Target.equal_reg reg) regs with
  | Some (index, _) -> index
  | None ->
    failwith
      (Format.asprintf "find_reg: couldn't find index for register %a"
         X86.Target.pp_reg reg)

let setup_register_shuffle ~(regs : X86.Target.reg array)
    ~(extra_curr_live : reg_mapping) ~(uses : reg_mapping) ~(defs : reg_mapping)
    ~(extra_clobbered_regs : reg_mapping) =
  let cfg = X86.Cfg.empty in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
  let select_state = Select_x86.State.init () in
  let block_execution_frequency _uid = 1. in
  let num_vregs =
    List.(
      length extra_curr_live + length uses + length defs
      + length extra_clobbered_regs)
  in
  let uid, instr_num = (2, 5) in
  select_state.curr_block <- uid;
  let vregs = Array.init num_vregs (fun _ -> select_state.fresh_vreg Int) in
  let live_through = Utils.IntHashtbl.create num_vregs in
  let dies _uid = function
    | X86.Target.Virtual vreg ->
      Some
        (if Utils.IntHashtbl.mem live_through vreg.id then instr_num + 1
         else instr_num)
    | _ -> None
  in
  let liveness =
    X86.Target.
      {
        Spill.X86.Liveness.live_in = (fun _ -> RegSet.empty);
        live_out = (fun _ -> RegSet.empty);
        used_in_block = (fun _ -> RegSet.empty);
        dies;
        max_register_pressure = (fun _ -> 0);
      }
  in
  let open Regalloc in
  let module Regalloc =
    Make (X86.Target) (X86.Cfg) (Select_x86.State) (Spill.X86.Liveness) (Dom)
  in
  let state =
    Regalloc.init_state ~select_state ~regs ~block_execution_frequency ~liveness
  in
  let idx phys = find_reg_index regs (X86.Target.Physical phys) in
  let set_reg idx = function
    | X86.Target.Virtual vreg -> vreg.reg <- regs.(idx)
    | _ -> failwith "Register not virtual"
  in
  let next_vreg =
    let c = ref (-1) in
    fun () ->
      incr c;
      !c
  in
  let setup_occupied (reg, is_live_through) =
    let vreg = vregs.(next_vreg ()) in
    CCBV.set state.occupied (idx reg);
    state.reg_current_var.(idx reg) <- Some (get_vreg vreg);
    state.reg_current_pref.(idx reg) <- float_of_int (get_vreg vreg).id;
    set_reg (idx reg) vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    vreg
  in
  let setup_constrained (reg, is_live_through) =
    let vreg = vregs.(next_vreg ()) in
    ignore @@ X86.Target.constrained reg vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    vreg
  in
  let clobbered = Utils.IntHashtbl.create num_vregs in
  let srcs = CCVector.create () in
  let dests = CCVector.create () in
  List.iter (fun t -> ignore (setup_occupied t)) extra_curr_live;
  List.iter (fun t -> CCVector.push srcs (setup_occupied t)) uses;
  List.iter (fun t -> CCVector.push dests (setup_constrained t)) defs;
  List.iter
    (fun t ->
      let vreg = setup_constrained t in
      Utils.IntHashtbl.replace clobbered (X86.Target.index vreg) true;
      CCVector.push dests vreg)
    extra_clobbered_regs;
  let old_vregs =
    Array.init (Array.length vregs) (fun i -> (get_vreg vregs.(i)).reg)
  in
  let to_operands l =
    List.map (fun r -> X86.Target.Reg r) (CCVector.to_list l)
  in
  let srcs, dests = (to_operands srcs, to_operands dests) in
  let instr = X86.Target.pcopy ~dests ~srcs in
  let head, instr =
    Regalloc.color_instruction state uid instr_num (X86.Cfg.First Entry) instr
  in
  Format.printf "Live through: %s\n"
    ([%show: (int * bool) list] (Utils.IntHashtbl.to_list live_through));
  let clobbered =
    List.fold_left
      (fun acc -> function
        | X86.Target.Reg (Virtual { reg_constr = UsePhysical phys; _ } as reg)
          ->
          X86.Target.RegMap.add (Physical phys) reg acc
        | _ -> acc)
      X86.Target.RegMap.empty
      (CCList.drop (List.length srcs) dests)
  in
  let id = X86.Target.index in
  let reg vreg = (get_vreg vreg).reg in
  let live_through_clobbered vreg =
    try
      let clobbered = X86.Target.RegMap.find (reg vreg) clobbered in
      Utils.IntHashtbl.mem live_through (id clobbered)
    with Not_found -> false
  in
  (* check that reg_current_var, reg_current_pref, and occupied are set correctly *)
  let rec check_vregs = function
    | X86.Target.Reg src :: srcs, X86.Target.Reg dest :: dests ->
      Format.printf "Virtual registers: %a -> %a\n" X86.Target.pp_reg src
        X86.Target.pp_reg dest;
      let mk_check s vreg =
        Format.asprintf "Virtual register %a's value for %s:" X86.Target.pp_reg
          vreg s
      in
      check bool (mk_check "occupied" src)
        (Utils.IntHashtbl.mem live_through (id src)
        || Utils.IntHashtbl.mem live_through (id dest)
        || live_through_clobbered src)
        (CCBV.get state.occupied (idx (get_physical (reg src))));
      check bool (mk_check "occupied" dest)
        (Utils.IntHashtbl.mem live_through (id dest)
        || live_through_clobbered dest)
        (CCBV.get state.occupied (idx (get_physical (reg dest))));
      check
        (option X86.Target.(testable pp_reg equal_reg))
        (mk_check "current var" src)
        (if live_through_clobbered src then
           Some (X86.Target.RegMap.find (reg src) clobbered)
         else if Utils.IntHashtbl.mem live_through (id src) then Some src
         else if Utils.IntHashtbl.mem live_through (id dest) then Some dest
         else None)
        (Option.map
           (fun vreg -> X86.Target.Virtual vreg)
           state.reg_current_var.(idx (get_physical (reg src))));
      check
        (option X86.Target.(testable pp_reg equal_reg))
        (mk_check "current var" dest)
        (if live_through_clobbered dest then
           Some (X86.Target.RegMap.find (reg dest) clobbered)
         else if Utils.IntHashtbl.mem live_through (id dest) then Some dest
         else None)
        (Option.map
           (fun vreg -> X86.Target.Virtual vreg)
           state.reg_current_var.(idx (get_physical (reg dest))));
      check (float 0.01)
        (mk_check "current preference" src)
        (if
           Utils.IntHashtbl.mem live_through (id src)
           || Utils.IntHashtbl.mem live_through (id dest)
         then float_of_int (get_vreg src).id
         else if live_through_clobbered src then float_of_int (get_vreg src).id
         else 0.)
        state.reg_current_pref.(idx (get_physical (reg src)));
      check_vregs (srcs, dests)
    | _ -> ()
  in
  check_vregs (srcs, dests);
  (old_vregs, vregs, X86.Cfg.Head (head, Instruction instr))

let test_pcopy_instr ~regs head =
  let dummy_reg = (-100, X86.Target.Int, "dummy") in
  let module Sequentialize =
    Seqpcopy.Make
      (X86.Cfg)
      (struct
        include X86.SeqpcopyRequirements
        let temp = Target.Reg (Physical dummy_reg)
      end) in
  let rec expand_pcopies tail = function
    | X86.Cfg.First _ -> tail
    | X86.Cfg.Head (head, Instruction instr) ->
      let instr =
        instr
        |> X86.Target.map_uses X86.Target.to_colored
        |> X86.Target.map_defs (function
          | X86.Target.Reg (Virtual { reg_constr = UsePhysical phys; _ }) ->
            Reg regs.(find_reg_index regs (Physical phys))
          | op -> op)
      in
      let tail = Sequentialize.parallel_copy_instr instr tail in
      expand_pcopies tail head
  in
  let tail = expand_pcopies (Last Exit) head in
  Format.printf "Expanded pcopies: %a\n" X86.Cfg.pp_tail tail;
  let init_state = ref X86.Target.RegMap.empty in
  Array.iteri
    (fun v reg -> init_state := X86.Target.RegMap.add reg v !init_state)
    regs;
  let init_state =
    X86.Target.RegMap.add (Physical dummy_reg) (-1) !init_state
  in
  let update_state state instr =
    let go state = function
      | X86.Target.Reg src, X86.Target.Reg dest ->
        Format.printf "Setting: %a to %d at %a\n" X86.Target.pp_reg dest
          (X86.Target.RegMap.find src state)
          X86.Target.pp_reg src;
        X86.Target.RegMap.(add dest (find src state) state)
      | _ -> failwith "Invalid srcs and dests"
    in
    List.(fold_left go state (combine instr.X86.Target.uses instr.defs))
  in
  let rec interpret_moves state = function
    | X86.Cfg.Tail (Instruction i, rest) ->
      interpret_moves (update_state state i) rest
    | X86.Cfg.Last _ -> state
  in
  let result_state = interpret_moves init_state tail in
  (init_state, result_state)

let clobber_constrained constrained state =
  fst
  @@ List.fold_left
       (fun (state, v) reg -> (X86.Target.RegMap.add reg v state, v - 1))
       (state, -1) constrained

let check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state =
  (* Check that values of the uses original registers are in the constrained registers *)
  let check_use (use, _) (def, _) =
    check int
      (Format.asprintf "Checking that %a was moved to %a" X86.Target.pp_reg
         (Physical use) X86.Target.pp_reg (Physical def))
      (X86.Target.RegMap.find (Physical use) init_state)
      (X86.Target.RegMap.find (Physical def) result_state)
  in
  List.iter2 check_use uses defs;
  (* Then clobber all the constrained defs *)
  let result_state =
    clobber_constrained
      (List.map
         (fun (phys, _) -> X86.Target.Physical phys)
         extra_clobbered_regs)
      result_state
  in
  (* Then check that the live through values before the instruction
       are still there after substitution *)
  let live_throughs =
    extra_curr_live @ uses
    |> List.mapi (fun i (_, live_through) -> (i, live_through))
    |> List.filter_map (fun (i, live_through) ->
        if live_through then Some i else None)
  in
  let check_live_through vreg =
    let vreg' = get_vreg vreg in
    check int
      (Format.asprintf
         "Checking that vreg %d was moved from %a to %a and is still live \
          through"
         vreg'.id X86.Target.pp_reg old_vregs.(vreg'.id) X86.Target.pp_reg
         vreg'.reg)
      (X86.Target.RegMap.find old_vregs.(vreg'.id) init_state)
      (X86.Target.RegMap.find vreg'.reg result_state)
  in
  List.iter check_live_through (List.map (fun i -> vregs.(i)) live_throughs)

(* [ rax; rbx; rcx; rdx; rsi; rdi; rsp; rbp; r8; r9; r10; r11; r12; r13; r14; r15; ] *)
let regs =
  X86.Regs.int_regs
  |> List.map (fun phys -> X86.Target.Physical phys)
  |> Array.of_list

let pick ?(regs = regs) =
  let regs = Array.copy regs in
  fun num ->
    CCArray.shuffle regs;
    Array.to_list regs |> CCList.take num

(* Invariants:

   length(defs) = length(uses)
   intersect(uses, extra_curr_live) = {}
   total_live_through = length(regs) - length(union(defs, extra_clobbered_regs))
   length(extra_curr_live) <= total_live_through
   length(extra_curr_live) + count(is_live_through, uses) = total_live_through
   def can't be live through if it is in extra_clobbered_regs
*)
let rec randomized_register_shuffle_test () =
  let get_random () = CCRandom.(run (int_range 1 (Array.length regs))) in
  let extra_curr_live = pick (get_random ()) in
  let extra_clobbered_regs = pick (get_random ()) in
  let uses =
    pick
      ~regs:
        (Array.of_list
           X86.Target.RegSet.(
             to_list
               (diff (of_list (Array.to_list regs)) (of_list extra_curr_live))))
      (get_random ())
  in
  let defs = pick (List.length uses) in
  let extra_clobbered_regs_set =
    X86.Target.RegSet.of_list extra_clobbered_regs
  in
  let num_live_through =
    Array.length regs
    - X86.Target.RegSet.(
        cardinal (union (of_list defs) extra_clobbered_regs_set))
  in
  if
    List.length uses = List.length defs
    && List.length extra_curr_live <= num_live_through
  then begin
    let num_live_uses = num_live_through - List.length extra_curr_live in
    let uses =
      let live, non_live = CCList.take_drop num_live_uses uses in
      let arr =
        Array.of_list
        @@ List.map (fun l -> (get_physical l, true)) live
        @ List.map (fun l -> (get_physical l, false)) non_live
      in
      CCArray.shuffle arr;
      Array.to_list arr
    in
    let extra_curr_live =
      List.map (fun l -> (get_physical l, true)) extra_curr_live
    in
    let extra_clobbered_regs =
      List.map
        (fun l -> (get_physical l, CCRandom.bool ()))
        extra_clobbered_regs
    in
    let defs =
      List.map
        (fun l ->
          ( get_physical l,
            if X86.Target.RegSet.mem l extra_clobbered_regs_set then false
            else CCRandom.bool () ))
        defs
    in
    let pp_phys fmt (phys, live_through) =
      if live_through then
        Format.fprintf fmt "!%a" X86.Target.pp_reg (Physical phys)
      else Format.fprintf fmt "%a" X86.Target.pp_reg (Physical phys)
    in
    let test_name =
      let pp_sep fmt () = Format.fprintf fmt "," in
      let pp_phys_list = Format.pp_print_list ~pp_sep pp_phys in
      Format.asprintf "live %a uses %a defs %a clob %a" pp_phys_list
        extra_curr_live pp_phys_list uses pp_phys_list defs pp_phys_list
        extra_clobbered_regs
    in
    test_case test_name `Quick @@ fun () ->
    Format.printf "Test: %s\n" test_name;
    let old_vregs, vregs, head =
      setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
        ~extra_clobbered_regs
    in
    Format.printf "Head: %a\n" X86.Cfg.pp_head head;
    let init_state, result_state = test_pcopy_instr ~regs head in
    check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
      ~old_vregs ~vregs ~init_state ~result_state
  end
  else randomized_register_shuffle_test ()

let test_register_shuffle1 () =
  (* vregs 0, 1, 2 are live through but not in the uses or defs of the instruction *)
  let extra_curr_live = X86.Regs.[ (rdi, true); (rsi, true); (rdx, true) ] in
  (* vregs 3, 4, 5, 6 are the uses of the instruction in callee save registers
     3, 4, and 6 die at the instruction, but 5 is live through *)
  let uses =
    X86.Regs.[ (r12, false); (r13, false); (rbx, true); (r9, false) ]
  in
  (* vregs 7, 8, 9, 10 are constrained to rdi, rsi, rdx, rcx *)
  let defs = List.map (fun r -> (r, false)) X86.Regs.[ rdi; rsi; rdx; rcx ] in
  (* vregs 11, 12, 13, 14, 15, 16, 17, 18, 19 are the constrained defs of the instruction
     the def for rax lives through the instruction but the rest die *)
  let extra_clobbered_regs =
    X86.Regs.
      [
        (rax, true);
        (rcx, false);
        (r8, false);
        (r9, false);
        (r10, false);
        (r11, false);
        (rdx, false);
        (rsi, false);
        (rdi, false);
      ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

(* Test: live !r13,!rdi uses rbp,!r8,r9,rsp,!rcx,r10,r15,rax defs !r12,!r11,!r14,!r13,!r15,!rsi,!rdx,!rsp clob !rax,!rbx,!r8,!r12,!rsp,!rdi *)
let test_register_shuffle2 () =
  let extra_curr_live = X86.Regs.[ (r13, true); (rdi, true) ] in
  let uses =
    X86.Regs.
      [
        (rbp, false);
        (r8, true);
        (r9, false);
        (rsp, false);
        (rcx, true);
        (r10, false);
        (r15, false);
        (rax, false);
      ]
  in
  let defs =
    List.map
      (fun r -> (r, true))
      X86.Regs.[ r12; r11; r14; r13; r15; rsi; rdx; rsp ]
  in
  let extra_clobbered_regs =
    List.map (fun r -> (r, true)) X86.Regs.[ rax; rbx; r8; r12; rsp; rdi ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

(* Test: live !r14 uses !r10,!r8 defs !rax,!rsi clob !rcx,!rdx,!r13,!r15,!rsi *)
let test_register_shuffle3 () =
  let extra_curr_live = X86.Regs.[ (r14, true) ] in
  let uses = X86.Regs.[ (r10, true); (r8, true) ] in
  let defs = List.map (fun r -> (r, true)) X86.Regs.[ rax; rsi ] in
  let extra_clobbered_regs =
    List.map (fun r -> (r, true)) X86.Regs.[ rcx; rdx; r13; r15; rsi ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

(* Test: live !rsi uses r12,r11 defs !r10,!rcx clob !r12,!r10,!rax,!r15,!rdx,!rbp,!rbx,!rdi,!r11,!r9,!r14,!r13,!rsp,!rcx,!r8 *)
let test_register_shuffle4 () =
  let extra_curr_live = X86.Regs.[ (rsi, true) ] in
  let uses = X86.Regs.[ (r12, false); (r11, false) ] in
  let defs = List.map (fun r -> (r, true)) X86.Regs.[ r10; rcx ] in
  let extra_clobbered_regs =
    List.map
      (fun r -> (r, true))
      X86.Regs.
        [
          r12;
          r10;
          rax;
          r15;
          rdx;
          rbp;
          rbx;
          rdi;
          r11;
          r9;
          r14;
          r13;
          rsp;
          rcx;
          r8;
        ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

(* Test: live !r10,!rdi,!rbx uses r8,rcx,!r11,rdx defs !rbp,rcx,r8,!r15 clob !r8,!r13,!rcx,r14,!rsi,r9,!rax,!rsp,r12,!rdx *)
let test_register_shuffle5 () =
  let extra_curr_live = X86.Regs.[ (r10, true); (rdi, true); (rbx, true) ] in
  let uses =
    X86.Regs.[ (r8, false); (rcx, false); (r11, true); (rdx, false) ]
  in
  let defs = X86.Regs.[ (rbp, true); (rcx, false); (r8, false); (r15, true) ] in
  let extra_clobbered_regs =
    X86.Regs.
      [
        (r8, true);
        (r13, true);
        (rcx, true);
        (r14, false);
        (rsi, true);
        (r9, false);
        (rax, true);
        (rsp, true);
        (r12, false);
        (rdx, true);
      ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

(* Test: live !rdx uses r15,rsp,r10,r12 defs !rbp,r9,r11,rsi clob r10,rcx,!r13,!r8,r14,r15,!rdi,!rsp,r9,rax,!r11,!r12,rbx,!rsi *)
let test_register_shuffle6 () =
  let extra_curr_live = X86.Regs.[ (rdx, true) ] in
  let uses = List.map (fun r -> (r, false)) X86.Regs.[ r15; rsp; r10; r12 ] in
  let defs =
    X86.Regs.[ (rbp, true); (r9, false); (r11, false); (rsi, false) ]
  in
  let extra_clobbered_regs =
    X86.Regs.
      [
        (r10, false);
        (rcx, false);
        (r13, true);
        (r8, true);
        (r14, false);
        (r15, false);
        (rdi, true);
        (rsp, true);
        (r9, false);
        (rax, false);
        (r11, true);
        (r12, true);
        (rbx, false);
        (rsi, true);
      ]
  in
  let old_vregs, vregs, head =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let init_state, result_state = test_pcopy_instr ~regs head in
  check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs
    ~old_vregs ~vregs ~init_state ~result_state

let _ =
  let _ = Random.set_state (Random.get_state ()) in
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  let randomized =
    List.init 100 (fun _ -> randomized_register_shuffle_test ())
  in
  run "Test_register_allocation"
    [
      ( "Tests_enforce_constraints",
        test_case "simple example" `Quick test_register_shuffle1
        :: test_case "swaps with live through" `Quick test_register_shuffle2
        :: test_case
             "test normal register shuffle doesn't assign register for \
              duplicate constrained def"
             `Quick test_register_shuffle3
        :: test_case "test live through clobbered reg occupies reg" `Quick
             test_register_shuffle4
        :: test_case "non-reassignment move to constrained live through" `Quick
             test_register_shuffle5
        :: test_case "non-reassignment move to constrained live through 2"
             `Quick test_register_shuffle6
        :: randomized );
    ]
