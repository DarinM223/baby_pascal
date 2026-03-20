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
    let _pass_through, temps =
      (Array.of_list (List.take 2 temps), List.drop 2 temps)
    in
    (* first_loop_temps are used in the body of the
       first loop and at the end of the program *)
    (* second_loop_temps are used at the beginning
       of the program and in the body of the second loop*)
    let _first_loop_temps, _second_loop_temps =
      (Array.of_list (List.take 8 temps), Array.of_list (List.drop 8 temps))
    in
    unfocus @@ init_temps @@ focus_entry empty
  in
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
