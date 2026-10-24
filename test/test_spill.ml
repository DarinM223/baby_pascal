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
    state.curr_block <- 1;
    let block1_arg1 = state.fresh_vreg Int in
    state.curr_block <- 2;
    let block2_arg1 = state.fresh_vreg Int in
    let block2_temp1 = state.fresh_vreg Int in
    let block2_temp2 = state.fresh_vreg Int in
    let block2_temp3 = state.fresh_vreg Int in
    let block2_temp4 = state.fresh_vreg Int in
    let block2_temp5 = state.fresh_vreg Int in
    let block2_temp6 = state.fresh_vreg Int in
    let block2_temp7 = state.fresh_vreg Int in
    state.curr_block <- 3;
    let block3_arg1 = state.fresh_vreg Int in
    state.curr_block <- 4;
    let block4_arg1 = state.fresh_vreg Int in
    state.curr_block <- 5;
    let block5_arg1 = state.fresh_vreg Int in
    let block5_temp1 = state.fresh_vreg Int in
    let block5_temp2 = state.fresh_vreg Int in
    let block5_temp3 = state.fresh_vreg Int in
    let block5_temp4 = state.fresh_vreg Int in
    let block5_temp5 = state.fresh_vreg Int in
    state.curr_block <- 6;
    let block6_arg1 = state.fresh_vreg Int in
    let block6_temp1 = state.fresh_vreg Int in
    let block6_temp2 = state.fresh_vreg Int in
    let block6_temp3 = state.fresh_vreg Int in
    state.curr_block <- 0;
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
  let module RegClass = struct
    module Target = X86.Target
    let reg_class = X86.Target.Int
    let k = 16
  end in
  let module X86Spill = Spill.X86 (RegClass) in
  let module NextUseDistances = X86Spill.NextUseDistances (Loop) in
  let next_use_distances = NextUseDistances.calc cfg in
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
  let liveness = X86Spill.Liveness.calc cfg in
  let module Spill =
    X86Spill.Make (Loop) (NextUseDistances)
      (struct
        let matches r = X86.Target.Reg.reg_class r = X86.Target.Int
        let k = 16
        let next_use_distances = next_use_distances
        let liveness = liveness
      end) in
  let state = Spill.init state in
  let cfg = Spill.spill state cfg in
  let expected =
    {|
  movq %49any, $17
  movq %48any, $16
  movq %47any, $15
  movq %46any, $14
  movq %45any, $13
  movq %44any, $12
  movq %43any, $11
  movq %42any, $10
  movq %41any, $9
  movq %40any, $8
  movq %39any, $7
  movq %38any, $6
  movq %37any, $5
  movq %36any, $4
  movq %35any, $3
  movq %34any, $2
  movq 0(%rsp), %48any
  movq %33any, $1
  movq 8(%rsp), %33any
  movq %32any, $0
  jmp label1(%41any)
label1(local=false)(50any):
  jl label3(%50any), label2(%50any), %35any, %34any
label2(local=false)(51any):
  addq %52any, %34any, %35any
  subq %53any, %52any, %34any
  mulq %54any, %36any, %51any, %37any
  addq %55any, %54any, %38any
  subq %56any, %39any, %40any
  addq %57any, %53any, %55any
  addq %58any, %57any, %56any, %54any
  jmp label1(%58any)
label3(local=false)(59any):
  movq %71any, 8(%rsp)
  movq %72any, 0(%rsp)
  jmp label4(%49any)
label4(local=false)(60any):
  jl label6(%60any), label5(%60any), %43any, %42any
label5(local=false)(61any):
  addq %62any, %42any, %43any
  subq %63any, %62any, %44any
  mulq %64any, %63any, %45any
  addq %65any, %64any, %46any
  subq %66any, %65any, %47any, %48any, %61any
  jmp label4(%66any)
label6(local=false)(67any):
  addq %68any, %32any, %33any
  addq %69any, %59any, %68any
  addq %70any, %67any, %69any
  ret %70any
|}
  in
  Logs.debug (fun m -> m "Spilled graph: %a\n" X86.Printer.pp_graph cfg);
  let cfg_pretty = Format.asprintf "%a" X86.Printer.pp_graph cfg in
  (check string) "Produces proper graph before SSA reconstruction" expected
    cfg_pretty;
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
      reg
      (Spill.RegSet.of_list copies)
      def_blocks graph
  in
  let cfg = Spill.RegHashtbl.fold reconstruct_copies state.copies cfg in
  Logs.debug (fun m -> m "Reconstructed graph: %a\n" X86.Printer.pp_graph cfg);
  let cfg_pretty = Format.asprintf "%a" X86.Printer.pp_graph cfg in
  let expected =
    {|
  movq %49any, $17
  movq %48any, $16
  movq %47any, $15
  movq %46any, $14
  movq %45any, $13
  movq %44any, $12
  movq %43any, $11
  movq %42any, $10
  movq %41any, $9
  movq %40any, $8
  movq %39any, $7
  movq %38any, $6
  movq %37any, $5
  movq %36any, $4
  movq %35any, $3
  movq %34any, $2
  movq 0(%rsp), %48any
  movq %33any, $1
  movq 8(%rsp), %33any
  movq %32any, $0
  jmp label1(%41any)
label1(local=false)(50any):
  jl label3(%50any), label2(%50any), %35any, %34any
label2(local=false)(51any):
  addq %52any, %34any, %35any
  subq %53any, %52any, %34any
  mulq %54any, %36any, %51any, %37any
  addq %55any, %54any, %38any
  subq %56any, %39any, %40any
  addq %57any, %53any, %55any
  addq %58any, %57any, %56any, %54any
  jmp label1(%58any)
label3(local=false)(59any):
  movq %71any, 8(%rsp)
  movq %72any, 0(%rsp)
  jmp label4(%49any)
label4(local=false)(60any):
  jl label6(%60any), label5(%60any), %43any, %42any
label5(local=false)(61any):
  addq %62any, %42any, %43any
  subq %63any, %62any, %44any
  mulq %64any, %63any, %45any
  addq %65any, %64any, %46any
  subq %66any, %65any, %47any, %72any, %61any
  jmp label4(%66any)
label6(local=false)(67any):
  addq %68any, %32any, %71any
  addq %69any, %59any, %68any
  addq %70any, %67any, %69any
  ret %70any
|}
  in
  (check string) "Check reconstructed graph" expected cfg_pretty

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Spilling"
    [ ("Tests spilling", [ test_case "spills in loops" `Quick test_loops ]) ]
