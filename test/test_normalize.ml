open Alcotest
open Baby_pascal

let test_example_1 () =
  let expr =
    Ast.
      [
        Assign ("a", Bop (Add, Int 1, Bop (Mul, Int 2, Int 3)));
        If
          ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
            [
              While
                ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
                  [ Assign ("a", Bop (Add, Var "a", Int 1)) ] );
            ],
            [ Assign ("result", Int 60) ] );
      ]
  in
  let result = Normalize.normalize expr in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" result Normalize.Cfg.empty

let _ =
  run "Normalize to zipper cfg"
    [ ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]) ]
