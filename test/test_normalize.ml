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
  let expected =
    let open Normalize.Cfg in
    let open Normalize.Target in
    unfocus
    @@ instruction
         (bop Ast.Mul ~src1:(Const 2) ~src2:(Const 3) ~dest:(reg "tmp1"))
    @@ instruction
         (bop Ast.Add ~src1:(Const 1) ~src2:(reg "tmp1") ~dest:(reg "tmp2"))
    @@ instruction (assign ~src:(reg "tmp2") ~dest:(reg "a"))
    @@ branch (8, "label8")
    @@ label (1, "label1")
    @@ exit
    @@ label (2, "label2")
    @@ branch (4, "label4")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(Const 60) ~dest:(reg "result"))
    @@ branch (1, "label1")
    @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" result expected

let _ =
  run "Normalize to zipper cfg"
    [ ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]) ]
