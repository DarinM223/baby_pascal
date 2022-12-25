open Alcotest
open Baby_pascal

module QuadArray = struct
  type t = Code.quad array [@@deriving show]

  let equal = ( = )
end

let test_example_1 () =
  Code.counter := -1;
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
            [ Return (Some (Int 60)) ] );
      ]
  in
  let result = expr |> Code.normalize |> CCVector.to_array in
  (check (module QuadArray))
    "same array" result
    Code.
      [|
        (Mul, Const 2, Const 3, Temp 0);
        (Add, Const 1, Temp 0, Temp 1);
        (Assign, Temp 1, Empty, Temp 2);
        (Eq, Temp 2, Const 1, Const 5);
        (Goto, Const 15, Empty, Empty);
        (Lt, Temp 2, Const 5, Const 7);
        (Goto, Const 15, Empty, Empty);
        (Eq, Temp 2, Const 1, Const 9);
        (Goto, Const 16, Empty, Empty);
        (Lt, Temp 2, Const 5, Const 11);
        (Goto, Const 16, Empty, Empty);
        (Add, Temp 2, Const 1, Temp 3);
        (Assign, Temp 3, Empty, Temp 2);
        (Goto, Const 7, Empty, Empty);
        (Goto, Const 16, Empty, Empty);
        (Return, Const 60, Empty, Empty);
        (Nop, Empty, Empty, Empty);
      |]

let _ =
  run "Test three address codegen"
    [ ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]) ]