open Alcotest
open Baby_pascal

let string =
  let pp fmt = Format.fprintf fmt "%s" in
  testable pp String.equal

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
      (Array.of_list (CCList.take 2 temps), CCList.drop 2 temps)
    in
    (* first_loop_temps are used in the body of the
       first loop and at the end of the program *)
    (* second_loop_temps are used at the beginning
       of the program and in the body of the second loop*)
    let first_loop_temps, second_loop_temps =
      (Array.of_list (CCList.take 8 temps), Array.of_list (CCList.drop 8 temps))
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
    @@ branch ~args:[ Reg first_loop_temps.(7) ] (1, "label1")
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
            ~uses:
              [
                Reg first_loop_temps.(2);
                Reg block2_arg1;
                Reg first_loop_temps.(3);
              ])
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
            ~uses:[ Reg block2_temp6; Reg block2_temp5; Reg block2_temp3 ])
    @@ branch ~args:[ Reg block2_temp7 ] (1, "label1")
    @@ label ~args:[ block3_arg1 ] (3, "label3")
    @@ branch ~args:[ Reg second_loop_temps.(7) ] (4, "label4")
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
                Reg block5_arg1;
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
  Logs.debug (fun m -> m "Initial graph: %a\n" X86.Printer.pp_graph cfg);
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (X86.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let next_use_distances = Spill.next_use_distances (module Loop) cfg in
  Logs.debug (fun m ->
      m "Next use distances: %s\n"
        begin
          let next_use_distances =
            X86.Cfg.reverse_postorder_dfs cfg
            |> List.map (fun block -> X86.Cfg.(idd (block_label block)))
            |> List.map (fun uid ->
                (uid, Spill.IntMap.to_list (next_use_distances.at_block uid)))
          in
          [%show: (int * (int * int) list) list] next_use_distances
        end);
  let liveness = Spill.Liveness.calc cfg in
  let module Spill =
    Spill.Make
      (Loop)
      (struct
        let k = 16
        let next_use_distances = next_use_distances
        let liveness = liveness
      end) in
  let state = Spill.init state in
  let cfg = Spill.spill state cfg in
  let expected =
    {|
  movq %17any, $17
  movq %16any, $16
  movq %15any, $15
  movq %14any, $14
  movq %13any, $13
  movq %12any, $12
  movq %11any, $11
  movq %10any, $10
  movq %9any, $9
  movq %8any, $8
  movq %7any, $7
  movq %6any, $6
  movq %5any, $5
  movq %4any, $4
  movq %3any, $3
  movq %2any, $2
  movq 0(%rsp), %16any
  movq %1any, $1
  movq 8(%rsp), %1any
  movq %0any, $0
  jmp label1(%9any)
label1(local=false)(18any):
  jl label3(%18any), label2(%18any), %3any, %2any
label2(local=false)(19any):
  addq %20any, %2any, %3any
  subq %21any, %20any, %2any
  mulq %22any, %4any, %19any, %5any
  addq %23any, %22any, %6any
  subq %24any, %7any, %8any
  addq %25any, %21any, %23any
  addq %26any, %25any, %24any, %22any
  jmp label1(%26any)
label3(local=false)(27any):
  movq %39any, 8(%rsp)
  movq %40any, 0(%rsp)
  jmp label4(%17any)
label4(local=false)(28any):
  jl label6(%28any), label5(%28any), %11any, %10any
label5(local=false)(29any):
  addq %30any, %10any, %11any
  subq %31any, %30any, %12any
  mulq %32any, %31any, %13any
  addq %33any, %32any, %14any
  subq %34any, %33any, %15any, %16any, %29any
  jmp label4(%34any)
label6(local=false)(35any):
  addq %36any, %0any, %1any
  addq %37any, %27any, %36any
  addq %38any, %35any, %37any
  ret %38any
|}
  in
  Logs.debug (fun m -> m "Spilled graph: %a\n" X86.Printer.pp_graph cfg);
  let cfg_pretty = Format.asprintf "%a" X86.Printer.pp_graph cfg in
  (check string) "Produces proper graph before SSA reconstruction" cfg_pretty
    expected;
  let module Reconstruct = Reconstruct.Make (X86.Target) (X86.Cfg) (Dom) in
  let reconstruct_copies reg _ graph =
    let copies = Spill.RegHashtbl.find_all state.copies reg in
    let def_blocks =
      List.map
        (fun r ->
          Deadcode.IntHashtbl.find state.select_state.vreg_block
            (X86.Target.index r))
        (reg :: copies)
    in
    Reconstruct.reconstruct
      (fun () -> state.select_state.fresh_vreg Int)
      (Spill.RegSet.singleton reg)
      (Spill.RegSet.of_list copies)
      def_blocks graph
  in
  let cfg = Spill.RegHashtbl.fold reconstruct_copies state.copies cfg in
  Logs.debug (fun m -> m "Reconstructed graph: %a\n" X86.Printer.pp_graph cfg);
  let cfg_pretty = Format.asprintf "%a" X86.Printer.pp_graph cfg in
  let expected =
    {|
  movq %17any, $17
  movq %16any, $16
  movq %15any, $15
  movq %14any, $14
  movq %13any, $13
  movq %12any, $12
  movq %11any, $11
  movq %10any, $10
  movq %9any, $9
  movq %8any, $8
  movq %7any, $7
  movq %6any, $6
  movq %5any, $5
  movq %4any, $4
  movq %3any, $3
  movq %2any, $2
  movq 0(%rsp), %16any
  movq %1any, $1
  movq 8(%rsp), %1any
  movq %0any, $0
  jmp label1(%9any)
label1(local=false)(18any):
  jl label3(%18any), label2(%18any), %3any, %2any
label2(local=false)(19any):
  addq %20any, %2any, %3any
  subq %21any, %20any, %2any
  mulq %22any, %4any, %19any, %5any
  addq %23any, %22any, %6any
  subq %24any, %7any, %8any
  addq %25any, %21any, %23any
  addq %26any, %25any, %24any, %22any
  jmp label1(%26any)
label3(local=false)(27any):
  movq %39any, 8(%rsp)
  movq %40any, 0(%rsp)
  jmp label4(%17any)
label4(local=false)(28any):
  jl label6(%28any), label5(%28any), %11any, %10any
label5(local=false)(29any):
  addq %30any, %10any, %11any
  subq %31any, %30any, %12any
  mulq %32any, %31any, %13any
  addq %33any, %32any, %14any
  subq %34any, %33any, %15any, %40any, %29any
  jmp label4(%34any)
label6(local=false)(35any):
  addq %36any, %0any, %39any
  addq %37any, %27any, %36any
  addq %38any, %35any, %37any
  ret %38any
|}
  in
  (check string) "Check reconstructed graph" cfg_pretty expected

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Spilling"
    [ ("Tests spilling", [ test_case "spills in loops" `Quick test_loops ]) ]
