open Alcotest
open Baby_pascal

let test_example_1 () =
  let cfg =
    (* let open Normalize.Target in *)
    let open Normalize.Cfg in
    unfocus @@ focus_entry empty
  in
  let expected =
    (* let open Normalize.Target in *)
    let open Normalize.Cfg in
    unfocus @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let _ =
  run "Dead code elimination"
    [ ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]) ]
