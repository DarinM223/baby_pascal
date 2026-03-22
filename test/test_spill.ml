open Alcotest
open Baby_pascal

let test_loops () =
  let state = Select_x86.State.init () in
  let cfg =
    let open X86.Target in
    let open X86.Cfg in
    let temps = List.init 18 (fun _ -> state.fresh_vreg Int) in
    let init_temps zgraph =
      fst
      @@ List.fold_left
           (fun (acc, i) tmp ->
             (instruction (mov ~dest:(Reg tmp) ~src:(Imm i)) @@ acc, i + 1))
           (zgraph, 0) temps
    in
    (* pass_through is variables not used in either loops
       but used at the beginning and end of the program *)
    let pass_through, temps =
      (Array.of_list (List.take 2 temps), List.drop 2 temps)
    in
    (* first_loop_temps are used in the body of the
       first loop and at the end of the program *)
    (* second_loop_temps are used at the beginning
       of the program and in the body of the second loop*)
    let first_loop_temps, second_loop_temps =
      (Array.of_list (List.take 8 temps), Array.of_list (List.drop 8 temps))
    in
    state.curr_block := 1;
    let block1_arg1 = state.fresh_vreg Int in
    state.curr_block := 2;
    let block2_arg1 = state.fresh_vreg Int in
    let block2_temp1 = state.fresh_vreg Int in
    let block2_temp2 = state.fresh_vreg Int in
    let block2_temp3 = state.fresh_vreg Int in
    let block2_temp4 = state.fresh_vreg Int in
    let block2_temp5 = state.fresh_vreg Int in
    let block2_temp6 = state.fresh_vreg Int in
    let block2_temp7 = state.fresh_vreg Int in
    state.curr_block := 3;
    let block3_arg1 = state.fresh_vreg Int in
    state.curr_block := 4;
    let block4_arg1 = state.fresh_vreg Int in
    state.curr_block := 5;
    let block5_arg1 = state.fresh_vreg Int in
    let block5_temp1 = state.fresh_vreg Int in
    let block5_temp2 = state.fresh_vreg Int in
    let block5_temp3 = state.fresh_vreg Int in
    let block5_temp4 = state.fresh_vreg Int in
    let block5_temp5 = state.fresh_vreg Int in
    state.curr_block := 6;
    let block6_arg1 = state.fresh_vreg Int in
    let block6_temp1 = state.fresh_vreg Int in
    let block6_temp2 = state.fresh_vreg Int in
    let block6_temp3 = state.fresh_vreg Int in
    state.curr_block := 0;
    unfocus @@ init_temps
    @@ branch (1, "label1")
    @@ label ~args:[ block1_arg1 ] (1, "label1")
    @@ cbranch ~ifso_args:[ Reg block1_arg1 ] ~ifnot_args:[ Reg block1_arg1 ]
         ~args:[ Reg first_loop_temps.(1); Reg first_loop_temps.(0) ]
         LT ~ifso:(3, "label3") ~ifnot:(2, "label2")
    @@ label ~args:[ block2_arg1 ] (2, "label2")
    @@ instruction
         (instr "addq" ~defs:[ Reg block2_temp1 ]
            ~uses:[ Reg first_loop_temps.(0); Reg first_loop_temps.(1) ])
    @@ instruction
         (instr "subq" ~defs:[ Reg block2_temp2 ]
            ~uses:[ Reg block2_temp1; Reg first_loop_temps.(0) ])
    @@ instruction
         (instr "mulq" ~defs:[ Reg block2_temp3 ]
            ~uses:[ Reg first_loop_temps.(2); Reg block2_arg1 ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block2_temp4 ]
            ~uses:[ Reg block2_temp3; Reg first_loop_temps.(4) ])
    @@ instruction
         (instr "subq" ~defs:[ Reg block2_temp5 ]
            ~uses:[ Reg first_loop_temps.(5); Reg first_loop_temps.(6) ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block2_temp6 ]
            ~uses:[ Reg block2_temp2; Reg block2_temp4 ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block2_temp7 ]
            ~uses:
              [ Reg block2_temp6; Reg block2_temp5; Reg first_loop_temps.(7) ])
    @@ branch ~args:[ Reg block2_temp7 ] (1, "label1")
    @@ label ~args:[ block3_arg1 ] (3, "label3")
    @@ label ~args:[ block4_arg1 ] (4, "label4")
    @@ cbranch ~ifso_args:[ Reg block4_arg1 ] ~ifnot_args:[ Reg block4_arg1 ]
         ~args:[ Reg second_loop_temps.(1); Reg second_loop_temps.(0) ]
         LT ~ifso:(6, "label6") ~ifnot:(5, "label5")
    @@ label ~args:[ block5_arg1 ] (5, "label5")
    @@ instruction
         (instr "addq" ~defs:[ Reg block5_temp1 ]
            ~uses:[ Reg second_loop_temps.(0); Reg second_loop_temps.(1) ])
    @@ instruction
         (instr "subq" ~defs:[ Reg block5_temp2 ]
            ~uses:[ Reg block5_temp1; Reg second_loop_temps.(2) ])
    @@ instruction
         (instr "mulq" ~defs:[ Reg block5_temp3 ]
            ~uses:[ Reg block5_temp2; Reg second_loop_temps.(3) ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block5_temp4 ]
            ~uses:[ Reg block5_temp3; Reg second_loop_temps.(4) ])
    @@ instruction
         (instr "subq" ~defs:[ Reg block5_temp5 ]
            ~uses:
              [
                Reg block5_temp4;
                Reg second_loop_temps.(5);
                Reg second_loop_temps.(6);
                Reg second_loop_temps.(7);
              ])
    @@ branch ~args:[ Reg block5_temp5 ] (4, "label4")
    @@ label ~args:[ block6_arg1 ] (6, "label6")
    @@ instruction
         (instr "addq" ~defs:[ Reg block6_temp1 ]
            ~uses:[ Reg pass_through.(0); Reg pass_through.(1) ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block6_temp2 ]
            ~uses:[ Reg block3_arg1; Reg block6_temp1 ])
    @@ instruction
         (instr "addq" ~defs:[ Reg block6_temp3 ]
            ~uses:[ Reg block6_arg1; Reg block6_temp2 ])
    @@ return ~uses:[ Reg block6_temp3 ]
    @@ focus_entry empty
  in
  Format.printf "Initial graph: %a\n" X86.Printer.pp_graph cfg;
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (X86.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let next_use_distances = Spill.next_use_distances (module Loop) cfg in
  let liveness = Spill.Liveness.calc cfg in
  let module Spill =
    Spill.Make
      (Loop)
      (struct
        let k = 16
        let next_use_distances = next_use_distances
        let liveness = liveness
      end)
  in
  let state = Spill.init state in
  let cfg = Spill.spill state cfg in
  let expected =
    (* let open X86.Target in *)
    let open X86.Cfg in
    empty
  in
  Format.printf "Spilled graph: %a\n" X86.Printer.pp_graph cfg;
  (check X86.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph before SSA reconstruction" cfg expected;
  let module Reconstruct = Reconstruct.Make (X86.Target) (X86.Cfg) (Dom) in
  (* todo: for every cloned register run reconstruct *)
  ()

let _ =
  run "Spilling"
    [ ("Tests spilling", [ test_case "spills in loops" `Quick test_loops ]) ]
