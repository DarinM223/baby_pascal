open Alcotest
open Baby_pascal

let test_simple () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "a"))
    @@ instruction (bop Add ~dest:(reg "b") ~src1:(reg "a") ~src2:(Const 1))
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "c"))
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "c") ~src2:(Const 1))
    @@ return ~uses:[ reg "b" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "a"))
    @@ instruction (bop Add ~dest:(reg "b") ~src1:(reg "a") ~src2:(Const 1))
    @@ return ~uses:[ reg "b" ]
    @@ focus_entry empty
  in
  let cfg, changed = Deadcode.M.deadcode cfg in
  (check bool) "Graph changed" true changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_branch () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "a"))
    @@ instruction (bop Add ~dest:(reg "b") ~src1:(reg "a") ~src2:(Const 1))
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "c"))
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "c") ~src2:(Const 1))
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "e"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "f"))
    @@ cbranch ~args:[ reg "f"; Const 0 ] EQ ~ifso:(1, "") ~ifnot:(2, "")
    @@ label (1, "")
    @@ instruction (bop Add ~dest:(reg "g") ~src1:(reg "a") ~src2:(Const 1))
    @@ return ~uses:[ reg "b" ]
    @@ label (2, "")
    @@ instruction (bop Add ~dest:(reg "h") ~src1:(reg "c") ~src2:(Const 1))
    @@ return ~uses:[ reg "d" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "a"))
    @@ instruction (bop Add ~dest:(reg "b") ~src1:(reg "a") ~src2:(Const 1))
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "c"))
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "c") ~src2:(Const 1))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "f"))
    @@ cbranch ~args:[ reg "f"; Const 0 ] EQ ~ifso:(1, "") ~ifnot:(2, "")
    @@ label (1, "")
    @@ return ~uses:[ reg "b" ]
    @@ label (2, "")
    @@ return ~uses:[ reg "d" ]
    @@ focus_entry empty
  in
  let cfg, changed = Deadcode.M.deadcode cfg in
  (check bool) "Graph changed" true changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_block_args () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "c"))
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "b"))
    @@ branch ~args:[ reg "a"; reg "b"; reg "c" ] (1, "")
    @@ label ~args:[ name "d"; name "e"; name "f" ] (1, "")
    @@ cbranch ~args:[ reg "e"; Const 0 ] EQ ~ifso:(2, "") ~ifnot:(3, "")
    @@ label (2, "")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "g"))
    @@ branch ~args:[ reg "g"; reg "h"; reg "i" ] (1, "")
    @@ label (3, "")
    @@ exit @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "b"))
    @@ branch ~args:[ reg "b" ] (1, "")
    @@ label ~args:[ name "e" ] (1, "")
    @@ cbranch ~args:[ reg "e"; Const 0 ] EQ ~ifso:(2, "") ~ifnot:(3, "")
    @@ label (2, "")
    @@ branch ~args:[ reg "h" ] (1, "")
    @@ label (3, "")
    @@ exit @@ focus_entry empty
  in
  let cfg, changed = Deadcode.M.deadcode cfg in
  (check bool) "Graph changed" true changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let _ =
  run "Dead code elimination"
    [
      ( "Tests proper output",
        [
          test_case "no control flow" `Quick test_simple;
          test_case "branch" `Quick test_branch;
          test_case "block arguments" `Quick test_block_args;
        ] );
    ]
