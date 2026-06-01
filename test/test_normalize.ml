open Alcotest
open Baby_pascal

let test_example_1 () =
  let expr =
    Ast.
      [
        Assign ("a", Bop (Add, Int 1, Bop (Mul, Int 2, Int 3)));
        If
          ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
            While
              ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
                Assign ("a", Bop (Add, Var "a", Int 1)) ),
            Assign ("result", Int 60) );
      ]
  in
  let module Fresh = Normalize.Fresh () in
  let result = Normalize.normalize Fresh.fresh expr in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
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
    @@ label (4, "label4")
    @@ cbranch
         ~args:[ reg "a"; Const 1 ]
         EQ ~ifso:(6, "label6") ~ifnot:(1, "label1")
    @@ label (5, "label5")
    @@ instruction
         (bop Ast.Add ~src1:(reg "a") ~src2:(Const 1) ~dest:(reg "tmp0"))
    @@ instruction (assign ~src:(reg "tmp0") ~dest:(reg "a"))
    @@ branch (4, "label4")
    @@ label (6, "label6")
    @@ cbranch
         ~args:[ reg "a"; Const 5 ]
         LT ~ifso:(5, "label5") ~ifnot:(1, "label1")
    @@ label (7, "label7")
    @@ cbranch
         ~args:[ reg "a"; Const 5 ]
         LT ~ifso:(2, "label2") ~ifnot:(3, "label3")
    @@ label (8, "label8")
    @@ cbranch
         ~args:[ reg "a"; Const 1 ]
         EQ ~ifso:(7, "label7") ~ifnot:(3, "label3")
    @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" result expected

let test_map_first_last () =
  let open Normalize.Target in
  let open Normalize.Cfg in
  let cfg =
    unfocus
    @@ label (1, "")
    @@ instruction (assign ~src:(Const 60) ~dest:(reg "result"))
    @@ branch (2, "")
    @@ label (2, "")
    @@ exit @@ focus_entry empty
  in
  let zblock, rest = focus 1 cfg in
  (* move to the right *)
  let zblock =
    match zblock with
    | head, Tail (mid, tail) -> (Head (head, mid), tail)
    | head, Last last -> (head, Last last)
  in
  let handle_first = function
    | Entry -> Entry
    | Label (label, info) ->
      Label (label, { info with args = [ name "a"; name "b" ] })
  in
  let handle_last = function
    | Exit -> Exit
    | Branch (_, l) -> Branch (goto l [ reg "a"; reg "b" ], l)
    | CBranch (_, _, _) -> failwith ""
    | Return _ -> failwith ""
  in
  let zblock = map_last handle_last (map_first handle_first zblock) in
  let expected =
    ( Head
        ( First
            (Label ((1, ""), { local = false; args = [ name "a"; name "b" ] })),
          Instruction (assign ~src:(Const 60) ~dest:(reg "result")) ),
      Last (Branch (goto (2, "") [ reg "a"; reg "b" ], (2, ""))) )
  in
  (check (testable pp_zblock equal_zblock))
    "Produces proper zipper" zblock expected;
  let cfg = unfocus (zblock, rest) in
  let expected =
    unfocus
    @@ label ~args:[ name "a"; name "b" ] (1, "")
    @@ instruction (assign ~src:(Const 60) ~dest:(reg "result"))
    @@ branch ~args:[ reg "a"; reg "b" ] (2, "")
    @@ label (2, "")
    @@ exit @@ focus_entry empty
  in
  (check (testable pp_graph equal_graph)) "Produces proper graph" cfg expected

let _ =
  run "Normalize to zipper cfg"
    [
      ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]);
      ( "Tests zipper operations",
        [ test_case "map_first and map_last" `Quick test_map_first_last ] );
    ]
