open Alcotest
open Baby_pascal

(* todo: registers live before enforce_constraints,
         registers live after enforce_constraints,
         assigned registers, etc *)

type reg_mapping = (X86.Target.physical_reg * bool) list

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
  select_state.curr_block := uid;
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
        Spill.Liveness.live_in = (fun _ -> RegSet.empty);
        live_out = (fun _ -> RegSet.empty);
        used_in_block = (fun _ -> RegSet.empty);
        dies;
        max_register_pressure = (fun _ -> 0);
      }
  in
  let open Regalloc in
  let state =
    init_state ~select_state ~regs ~block_execution_frequency ~liveness
      (module Dom)
  in
  let idx phys = find_reg_index regs (X86.Target.Physical phys) in
  let set_reg idx = function
    | X86.Target.Virtual vreg ->
      vreg.reg <- regs.(idx);
      state.reg_current_var.(idx) <- Some vreg;
      state.reg_current_pref.(idx) <- state.preferences.%(vreg.id).(idx)
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
    set_reg (idx reg) vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    X86.Target.Reg vreg
  in
  let setup_constrained (reg, is_live_through) =
    let vreg = vregs.(next_vreg ()) in
    ignore @@ X86.Target.constrained reg vreg;
    if is_live_through then
      Utils.IntHashtbl.replace live_through (X86.Target.index vreg) true;
    X86.Target.Reg vreg
  in
  let srcs = CCVector.create () in
  let dests = CCVector.create () in
  List.iter (fun t -> ignore (setup_occupied t)) extra_curr_live;
  List.iter (fun t -> CCVector.push srcs (setup_occupied t)) uses;
  List.iter (fun t -> CCVector.push dests (setup_constrained t)) defs;
  List.iter
    (fun t -> CCVector.push dests (setup_constrained t))
    extra_clobbered_regs;
  let instr =
    X86.Target.pcopy ~dests:(CCVector.to_list dests)
      ~srcs:(CCVector.to_list srcs)
  in
  (vregs, enforce_constraints_pcopy state uid instr_num instr)

let test_pcopy_instr ~regs instr =
  let dummy_reg = (-100, X86.Target.Int, "dummy") in
  let module Sequentialize =
    Seqpcopy.Make
      (X86.Cfg)
      (struct
        include X86.SeqpcopyRequirements
        let temp = Target.Reg (Physical dummy_reg)
      end) in
  let tail = X86.Sequentialize.parallel_copy_instr instr (Last Exit) in
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
        X86.Target.RegMap.(add dest (find src state) state)
      | _ -> state
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

let subst_reg reg subst = X86.Target.RegMap.get_or ~default:reg reg subst
let get_vreg vreg =
  match vreg with
  | X86.Target.Virtual vreg -> vreg
  | _ -> failwith "Not a virtual register"

let check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs ~vregs
    ~subst ~init_state ~result_state =
  (* Check that values of the uses original registers are in the constrained registers *)
  let check_use (use, _) (def, _) =
    check int
      (Format.asprintf "Checking that %a was moved to %a" X86.Target.pp_reg
         (Physical use) X86.Target.pp_reg (Physical def))
      (X86.Target.RegMap.find (Physical def) result_state)
      (X86.Target.RegMap.find (Physical use) init_state)
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
    let subst_vreg = subst_reg vreg subst in
    let subst_vreg' = get_vreg subst_vreg in
    check int
      (Format.asprintf
         "Checking that %a was moved to %a and is still live through"
         X86.Target.pp_reg vreg X86.Target.pp_reg subst_vreg)
      (X86.Target.RegMap.find subst_vreg'.reg result_state)
      (X86.Target.RegMap.find vreg'.reg init_state)
  in
  List.iter check_live_through (List.map (fun i -> vregs.(i)) live_throughs)

let test_register_shuffle1 () =
  (* [ rax; rbx; rcx; rdx; rsi; rdi; rsp; rbp; r8; r9; r10; r11; r12; r13; r14; r15; ] *)
  let regs =
    X86.Regs.int_regs
    |> List.map (fun phys -> X86.Target.Physical phys)
    |> Array.of_list
  in
  let idx phys = Regalloc.find_reg_index regs (X86.Target.Physical phys) in
  (* vregs 0, 1, 2 are live through but not in the uses or defs of the instruction *)
  let extra_curr_live = X86.Regs.[ (rdi, true); (rsi, true); (rdx, true) ] in
  (* vregs 3, 4, 5, 6 are the uses of the instruction in callee save registers
     3, 4, and 6 die at the instruction, but 5 is live through *)
  let uses =
    X86.Regs.[ (r12, false); (r13, false); (rbx, true); (r9, false) ]
  in
  (* vregs 7, 8, 9, 10 are constrained to rdi, rsi, rdx, rcx *)
  let defs = List.map (fun r -> (r, true)) X86.Regs.[ rdi; rsi; rdx; rcx ] in
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
  let vregs, result =
    setup_register_shuffle ~regs ~extra_curr_live ~uses ~defs
      ~extra_clobbered_regs
  in
  let num_vregs = Array.length vregs in
  let result_testable =
    option
      X86.Target.(
        pair
          (testable pp_instr equal_instr)
          (testable (RegMap.pp pp_reg pp_reg) (RegMap.equal equal_reg)))
  in
  let fresh_vreg ~id ~phys =
    X86.Target.Virtual
      {
        id;
        reg_class = Int;
        reg_constr = UsePhysical phys;
        reg = regs.(idx phys);
      }
  in
  let new_rsp = fresh_vreg ~id:num_vregs ~phys:X86.Regs.rsp in
  let new_r12 = fresh_vreg ~id:(num_vregs + 1) ~phys:X86.Regs.r12 in
  let new_r13 = fresh_vreg ~id:(num_vregs + 2) ~phys:X86.Regs.r13 in
  let expected_instr =
    X86.Target.pcopy
      ~dests:
        (List.map
           (fun r -> X86.Target.Reg r)
           [
             new_r13;
             new_r12;
             new_rsp;
             vregs.(7);
             vregs.(8);
             vregs.(9);
             vregs.(10);
           ])
      ~srcs:
        (List.map (fun i -> X86.Target.Reg vregs.(i)) [ 1; 0; 2; 3; 4; 5; 6 ])
  in
  let expected_subst =
    X86.Target.RegMap.of_list
      [
        (vregs.(0), new_r12);
        (vregs.(1), new_r13);
        (vregs.(2), new_rsp);
        (vregs.(3), vregs.(7));
        (vregs.(4), vregs.(8));
        (vregs.(6), vregs.(10));
      ]
  in
  begin match result with
  | Some (instr, subst) ->
    let init_state, result_state = test_pcopy_instr ~regs instr in
    check_result_state ~extra_curr_live ~uses ~defs ~extra_clobbered_regs ~vregs
      ~subst ~init_state ~result_state
  | None -> ()
  end;
  check result_testable "Check result instruction and substitution map" result
    (Some (expected_instr, expected_subst))

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Test register allocation"
    [
      ( "Tests enforce_constraints",
        [ test_case "simple example" `Quick test_register_shuffle1 ] );
    ]
