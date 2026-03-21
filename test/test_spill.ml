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
    state.curr_block := 6;
    let temp1 = state.fresh_vreg Int in
    let temp2 = state.fresh_vreg Int in
    let temp3 = state.fresh_vreg Int in
    state.curr_block := 0;
    unfocus @@ init_temps
    @@ branch (1, "label1")
    @@ label (1, "label1")
    @@ cbranch
         ~args:[ Reg first_loop_temps.(1); Reg first_loop_temps.(0) ]
         LT ~ifso:(3, "label3") ~ifnot:(2, "label2")
    @@ label (2, "label2")
    @@ instruction
         (instr "addq"
            ~defs:[ Reg first_loop_temps.(1) ]
            ~uses:[ Reg first_loop_temps.(0); Imm 1 ])
    @@ instruction
         (instr "subq"
            ~defs:[ Reg first_loop_temps.(2) ]
            ~uses:[ Reg first_loop_temps.(1); Reg first_loop_temps.(0) ])
    @@ instruction
         (instr "mulq"
            ~defs:[ Reg first_loop_temps.(3) ]
            ~uses:[ Reg first_loop_temps.(2); Reg first_loop_temps.(2) ])
    @@ instruction
         (instr "addq"
            ~defs:[ Reg first_loop_temps.(5) ]
            ~uses:[ Reg first_loop_temps.(3); Reg first_loop_temps.(4) ])
    @@ instruction
         (instr "subq"
            ~defs:[ Reg first_loop_temps.(7) ]
            ~uses:[ Reg first_loop_temps.(5); Reg first_loop_temps.(6) ])
    @@ branch (1, "label1")
    @@ label (4, "label4")
    @@ cbranch
         ~args:[ Reg second_loop_temps.(1); Reg second_loop_temps.(0) ]
         LT ~ifso:(6, "label6") ~ifnot:(5, "label5")
    @@ label (5, "label5")
    @@ instruction
         (instr "addq"
            ~defs:[ Reg second_loop_temps.(1) ]
            ~uses:[ Reg second_loop_temps.(0); Imm 1 ])
    @@ instruction
         (instr "subq"
            ~defs:[ Reg second_loop_temps.(2) ]
            ~uses:[ Reg second_loop_temps.(1); Reg second_loop_temps.(0) ])
    @@ instruction
         (instr "mulq"
            ~defs:[ Reg second_loop_temps.(3) ]
            ~uses:[ Reg second_loop_temps.(2); Reg second_loop_temps.(2) ])
    @@ instruction
         (instr "addq"
            ~defs:[ Reg second_loop_temps.(5) ]
            ~uses:[ Reg second_loop_temps.(3); Reg second_loop_temps.(4) ])
    @@ instruction
         (instr "subq"
            ~defs:[ Reg second_loop_temps.(7) ]
            ~uses:[ Reg second_loop_temps.(5); Reg second_loop_temps.(6) ])
    @@ label (3, "label3")
    @@ branch (4, "label4")
    @@ branch (4, "label4")
    @@ label (6, "label6")
    @@ instruction
         (instr "addq" ~defs:[ Reg temp1 ]
            ~uses:[ Reg pass_through.(0); Reg pass_through.(1) ])
    @@ instruction
         (instr "addq" ~defs:[ Reg temp2 ]
            ~uses:[ Reg first_loop_temps.(7); Reg temp1 ])
    @@ instruction
         (instr "addq" ~defs:[ Reg temp3 ]
            ~uses:[ Reg second_loop_temps.(7); Reg temp2 ])
    @@ return ~uses:[ Reg temp3 ] @@ focus_entry empty
  in
  Format.printf "%a\n" X86.Printer.pp_graph cfg;
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
  (check X86.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph before SSA reconstruction" cfg expected;
  let module Reconstruct = Reconstruct.Make (X86.Target) (X86.Cfg) (Dom) in
  (* todo: for every cloned register run reconstruct *)
  ()

let _ =
  run "Spilling"
    [ ("Tests spilling", [ test_case "spills in loops" `Quick test_loops ]) ]
