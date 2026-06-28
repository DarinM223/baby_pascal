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
  let dies _uid _reg : int option = failwith "" in
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
  let regs = [||] in
  let state =
    Regalloc.init_state ~select_state ~regs ~block_execution_frequency ~liveness
      (module Dom)
  in
  (* todo: set currently occupied registers in state *)
  let uid, instr_num = (2, 5) in
  (* todo: fill out instr *)
  let instr = X86.Target.mov ~dest:(Reg Tombstone) ~src:(Reg Tombstone) in
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
