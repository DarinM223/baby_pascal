open Alcotest
open Baby_pascal

(*
           0
           |
           1 (label6)
           |
           2 (label2)<--+
          / \           |
(label1) 6   3 (label3) |
             |          |
    (label4) 4<+--------+
             | |
    (label5) 5-+
*)
let test_nested_loops () =
  let ast =
    let open Ast in
    [
      Assign ("i", Int 0);
      While
        ( Bop (Lt, Var "i", Int 100),
          [
            Assign ("j", Var "i");
            While
              ( Bop (Lt, Var "j", Int 100),
                [
                  Assign ("j", Bop (Add, Var "j", Int 1));
                  Assign ("i", Bop (Add, Var "i", Int 1));
                ] );
          ] );
    ]
  in
  let module F = Normalize.Fresh () in
  let cfg = Normalize.normalize F.fresh ast in
  let _, cfg = Select_x86.(codegen_test_helper (State.init ()) cfg) in
  Logs.debug (fun m -> m "%a" X86.Printer.pp_graph cfg);
  let extra = X86.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (X86.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (X86.Cfg) (Dom) in
  let module Freq = Execfreq.Make (X86.Cfg) (Loop) (X86.ExecfreqRequirements) in
  (check (array (float 0.1)))
    "Execution frequencies per block" Freq.bfreq
    [| 1.; 1.; 5.; 4.; 4.54545; 0.545455; 1. |]

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Test Block Execution Frequency"
    [
      ( "Test frequency calculation",
        [ test_case "nested loops" `Quick test_nested_loops ] );
    ]
