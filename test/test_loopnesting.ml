open Alcotest
open Baby_pascal

(*
   0
   |
   6
   |
   2 <-+
  / \  |
 1   3 |
      \|
       4 <-+
       |   |
       |  /
       | /
       5
*)
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
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Loop = Loopnesting.Make (Normalize.Cfg) (Dom) in
  Format.printf "Graph: %a\n" Normalize.Cfg.pp_graph cfg;
  let expected =
    Loop.PositionSet.of_list
      [
        Loop.Dom.position_of_label (Some (2, ""));
        Loop.Dom.position_of_label (Some (4, ""));
      ]
  in
  (check Loop.PositionSet.(testable pp equal))
    "Loop headers" Loop.loop_headers expected;
  let nodes =
    [|
      None;
      Some (6, "");
      Some (2, "");
      Some (3, "");
      Some (4, "");
      Some (5, "");
      Some (1, "");
    |]
  in
  for i = 0 to 6 do
    (check int) "Labels match with positions"
      (Dom.position_of_label nodes.(i))
      i
  done;
  let expected =
    Loop.PositionSet.
      [|
        of_list [ 0; 1; 2; 6 ];
        empty;
        of_list [ 3; 4 ];
        empty;
        singleton 5;
        empty;
        empty;
      |]
  in
  (check (array Loop.PositionSet.(testable pp equal)))
    "Loop nodes"
    (Iarray.to_array Loop.loop_nodes)
    expected

let _ =
  run "Loop nesting"
    [
      ( "Tests loop headers",
        [ test_case "nested loops" `Quick test_nested_loops_headers ] );
    ]
