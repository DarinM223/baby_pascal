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
  let num_vregs = 15 in
  let vregs = Array.init num_vregs (fun _ -> select_state.fresh_vreg Int) in
  let live_through = CCBV.create ~size:num_vregs false in
  let uid, instr_num = (2, 5) in
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
  let state =
    Regalloc.init_state ~select_state ~regs ~block_execution_frequency ~liveness
      (module Dom)
  in
  (* todo: set currently occupied registers in state *)
  let idx phys = Regalloc.find_reg_index regs (X86.Target.Physical phys) in
  let set_reg idx = function
    | X86.Target.Virtual vreg ->
      vreg.reg <- regs.(idx);
      state.reg_current_var.(idx) <- Some vreg;
      state.reg_current_pref.(idx) <- state.preferences.(vreg.id).(idx)
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

  (* vregs 6, 7, 8 are constrained to rdi, rsi, rdx *)
  ignore @@ X86.Target.constrained X86.Regs.rdi vregs.(6);
  CCBV.set live_through (X86.Target.index vregs.(6));
  ignore @@ X86.Target.constrained X86.Regs.rsi vregs.(7);
  CCBV.set live_through (X86.Target.index vregs.(7));
  ignore @@ X86.Target.constrained X86.Regs.rdx vregs.(8);
  CCBV.set live_through (X86.Target.index vregs.(8));

  (* vregs 9, 10, 11, 12, 13, 14 are the constrained defs of the instruction
     the def for rax lives through the instruction but the rest die *)
  ignore @@ X86.Target.constrained X86.Regs.rax vregs.(9);
  CCBV.set live_through (X86.Target.index vregs.(9));
  ignore @@ X86.Target.constrained X86.Regs.rcx vregs.(10);
  ignore @@ X86.Target.constrained X86.Regs.r8 vregs.(11);
  ignore @@ X86.Target.constrained X86.Regs.r9 vregs.(12);
  ignore @@ X86.Target.constrained X86.Regs.r10 vregs.(13);
  ignore @@ X86.Target.constrained X86.Regs.r11 vregs.(14);
  let instr =
    X86.Target.pcopy
      ~dests:
        ([ 6; 7; 8; 9; 10; 11; 12; 13; 14 ]
        |> List.map (fun i -> X86.Target.Reg vregs.(i)))
      ~srcs:([ 3; 4; 5 ] |> List.map (fun i -> X86.Target.Reg vregs.(i)))
  in
  let result = Regalloc.enforce_constraints_pcopy state uid instr_num instr in
  let result_testable =
    option
      X86.Target.(
        pair
          (testable pp_instr equal_instr)
          Regalloc.(testable (RegMap.pp pp_reg pp_reg) (RegMap.equal equal_reg)))
  in
  check result_testable "Check result instruction and substitution map" result
    None

let _ =
  run "Test register allocation"
    [
      ( "Tests enforce_constraints",
        [ test_case "simple example" `Quick test_register_shuffle1 ] );
    ]
