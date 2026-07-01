open Alcotest
open Baby_pascal

(* todo: registers live before enforce_constraints,
         registers live after enforce_constraints,
         assigned registers, etc *)

let test_register_shuffle1 () =
  (* let enforce_constraints_pcopy state uid instr_num instr = *)
  let cfg = X86.Cfg.empty in
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Dom = Dominator.Make (X86.Cfg) ((val extra)) in
  let select_state = Select_x86.State.init () in
  let block_execution_frequency _uid = 1. in
  let num_vregs = 18 in
  let uid, instr_num = (2, 5) in
  select_state.curr_block := uid;
  let vregs = Array.init num_vregs (fun _ -> select_state.fresh_vreg Int) in
  let live_through = CCBV.create ~size:num_vregs false in
  let dies _uid = function
    | X86.Target.Virtual vreg ->
      Some (if CCBV.get live_through vreg.id then instr_num + 1 else instr_num)
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
  (* [ rax; rbx; rcx; rdx; rsi; rdi; rsp; rbp; r8; r9; r10; r11; r12; r13; r14; r15; ] *)
  let regs =
    X86.Regs.int_regs
    |> List.map (fun phys -> X86.Target.Physical phys)
    |> Array.of_list
  in
  let open Regalloc in
  let state =
    init_state ~select_state ~regs ~block_execution_frequency ~liveness
      (module Dom)
  in
  (* todo: set currently occupied registers in state *)
  let idx phys = find_reg_index regs (X86.Target.Physical phys) in
  let set_reg idx = function
    | X86.Target.Virtual vreg ->
      vreg.reg <- regs.(idx);
      state.reg_current_var.(idx) <- Some vreg;
      state.reg_current_pref.(idx) <- state.preferences.%(vreg.id).(idx)
    | _ -> failwith "Register not virtual"
  in
  (* vregs 0, 1, 2 are live through but not in the uses or defs of the instruction *)
  CCBV.set state.occupied (idx X86.Regs.rdi);
  Format.printf "Vregs: %a\n" (CCArray.pp X86.Target.pp_reg) vregs;
  Format.printf "Idx: %d\n" (idx X86.Regs.rdi);
  set_reg (idx X86.Regs.rdi) vregs.(0);
  CCBV.set live_through (X86.Target.index vregs.(0));

  CCBV.set state.occupied (idx X86.Regs.rsi);
  set_reg (idx X86.Regs.rsi) vregs.(1);
  CCBV.set live_through (X86.Target.index vregs.(1));

  CCBV.set state.occupied (idx X86.Regs.rdx);
  set_reg (idx X86.Regs.rdx) vregs.(2);
  CCBV.set live_through (X86.Target.index vregs.(2));

  (* vregs 3, 4, 5 are the uses of the instruction in callee save registers
     3 and 4 die at the instruction, but 5 is live through *)
  CCBV.set state.occupied (idx X86.Regs.r12);
  set_reg (idx X86.Regs.r12) vregs.(3);
  CCBV.set state.occupied (idx X86.Regs.r13);
  set_reg (idx X86.Regs.r13) vregs.(4);
  CCBV.set state.occupied (idx X86.Regs.rbx);
  set_reg (idx X86.Regs.rbx) vregs.(5);
  CCBV.set live_through (X86.Target.index vregs.(5));

  check bool "Vreg 4 dies at instruction"
    (dies state uid vregs.(4) instr_num)
    true;
  check bool "Vreg 5 doesn't die at instruction"
    (dies state uid vregs.(5) instr_num)
    false;

  (* vregs 6, 7, 8 are constrained to rdi, rsi, rdx *)
  ignore @@ X86.Target.constrained X86.Regs.rdi vregs.(6);
  CCBV.set live_through (X86.Target.index vregs.(6));
  ignore @@ X86.Target.constrained X86.Regs.rsi vregs.(7);
  CCBV.set live_through (X86.Target.index vregs.(7));
  ignore @@ X86.Target.constrained X86.Regs.rdx vregs.(8);
  CCBV.set live_through (X86.Target.index vregs.(8));

  (* vregs 9, 10, 11, 12, 13, 14, 15, 16, 17 are the constrained defs of the instruction
     the def for rax lives through the instruction but the rest die *)
  ignore @@ X86.Target.constrained X86.Regs.rax vregs.(9);
  CCBV.set live_through (X86.Target.index vregs.(9));
  ignore @@ X86.Target.constrained X86.Regs.rcx vregs.(10);
  ignore @@ X86.Target.constrained X86.Regs.r8 vregs.(11);
  ignore @@ X86.Target.constrained X86.Regs.r9 vregs.(12);
  ignore @@ X86.Target.constrained X86.Regs.r10 vregs.(13);
  ignore @@ X86.Target.constrained X86.Regs.r11 vregs.(14);
  ignore @@ X86.Target.constrained X86.Regs.rdx vregs.(15);
  ignore @@ X86.Target.constrained X86.Regs.rsi vregs.(16);
  ignore @@ X86.Target.constrained X86.Regs.rdi vregs.(17);
  let instr =
    X86.Target.pcopy
      ~dests:
        ([ 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17 ]
        |> List.map (fun i -> X86.Target.Reg vregs.(i)))
      ~srcs:([ 3; 4; 5 ] |> List.map (fun i -> X86.Target.Reg vregs.(i)))
  in
  let result = enforce_constraints_pcopy state uid instr_num instr in
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
  let new_rbx = fresh_vreg ~id:num_vregs ~phys:X86.Regs.rbx in
  let new_r12 = fresh_vreg ~id:(num_vregs + 1) ~phys:X86.Regs.r12 in
  let new_r13 = fresh_vreg ~id:(num_vregs + 2) ~phys:X86.Regs.r13 in
  let expected_instr =
    X86.Target.pcopy
      ~dests:
        (List.map
           (fun r -> X86.Target.Reg r)
           [ new_r13; new_r12; vregs.(6); vregs.(7); vregs.(8); new_rbx ])
      ~srcs:(List.map (fun i -> X86.Target.Reg vregs.(i)) [ 2; 0; 3; 4; 5; 1 ])
  in
  let expected_subst =
    RegMap.of_list
      [
        (vregs.(0), new_r12);
        (vregs.(1), new_rbx);
        (vregs.(2), new_r13);
        (vregs.(3), vregs.(6));
        (vregs.(4), vregs.(7));
        (vregs.(5), vregs.(8));
      ]
  in
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
