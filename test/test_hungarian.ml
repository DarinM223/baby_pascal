open Alcotest
open Baby_pascal

let test_basic () =
  (* Worker/Task | Clean bathroom | Sweep floors | Wash windows
     ------------+----------------+--------------+-------------
        Alice    |      $8        |      $4      |     $7
        Bob      |      $5        |      $2      |     $3
        Carol    |      $9        |      $4      |     $8
  *)
  let cost = [| 8; 4; 7; 5; 2; 3; 9; 4; 8 |] in
  let result = Hungarian.solve ~cost ~num_rows:3 ~num_cols:3 in
  (* Assignments: (0, 0), (1, 2), (2, 1) *)
  let expected = [| 0; 2; 1 |] in
  (check (array int)) "assignments" expected result

let test_example () =
  let cost =
    [| 9; 0; 8; 0; 0; 0; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 9; 0; 0; 0; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 8; 8; 8; 0; 8; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 8; 8; 8; 8; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 9; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 8; 9; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 9; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 9; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 8; 9; 8; 0; 0; 8; 8;
       8; 0; 8; 0; 0; 0; 8; 8; 8; 8; 8; 9; 0; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 8; 8;
       8; 0; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 9; 8;
       8; 0; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 0; 0; 8; 9
    |] [@@ocamlformat "disable"]
  in
  let result = Hungarian.solve ~cost ~num_rows:16 ~num_cols:16 in
  let expected = [| 1; 0; 3; 2; 4; 5; 7; 6; 9; 8; 11; 10; 12; 13; 15; 14 |] in
  (check (array int)) "assignments" expected result

let _ =
  run "Test Hungarian algorithm"
    [
      ( "Test bipartite matching",
        [
          test_case "basic" `Quick test_basic;
          test_case "regalloc example" `Quick test_example;
        ] );
    ]
