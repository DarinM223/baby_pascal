open Alcotest
open Baby_pascal

let test_nested_loops_headers () =
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
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra =
    (val extra
        : Graph.Extra with type graph = Normalize.Cfg.graph
         and type label = Normalize.Target.label)
  in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (Normalize.Cfg) (Dom) in
  Format.printf "Graph: %a\n" Normalize.Cfg.pp_graph cfg;
  let expected = Loopnesting.LabelSet.of_list [ 2; 4 ] in
  (check Loopnesting.LabelSet.(testable pp equal))
    "Loop headers" Loop.loop_headers expected

let _ =
  run "Loop nesting"
    [
      ( "Tests loop headers",
        [ test_case "nested loops" `Quick test_nested_loops_headers ] );
    ]
