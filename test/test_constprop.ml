open Alcotest
open Baby_pascal

let test_block_args () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch ~args:[ reg "a"; reg "b"; reg "c" ] (1, "")
    @@ label ~args:[ name "d"; name "e"; name "f" ] (1, "")
    @@ cbranch ~args:[ reg "e"; Const 0 ] EQ ~ifso:(2, "") ~ifnot:(3, "")
    @@ label (2, "")
    @@ branch ~args:[ reg "g"; reg "h"; Const 1 ] (1, "")
    @@ label (3, "")
    @@ exit @@ focus_entry empty
  in
  let expected =
    Constprop.(
      NameMap.of_list
        Normalize.Target.
          [
            (name "d", OperandSet.of_list [ (0, reg "a"); (2, reg "g") ]);
            (name "e", OperandSet.of_list [ (0, reg "b"); (2, reg "h") ]);
            (name "f", OperandSet.of_list [ (0, reg "c"); (2, Const 1) ]);
          ])
  in
  let result = Constprop.block_args cfg in
  (check
     Constprop.(
       testable (NameMap.pp OperandSet.pp) (NameMap.equal OperandSet.equal)))
    "Produces proper mapping" result expected

let test_const_prop_simple () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ label (1, "")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (bop Ast.Add ~src1:(Const 1) ~src2:(reg "a") ~dest:(reg "b"))
    @@ return ~uses:[ reg "b" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus @@ label (1, "") @@ return ~uses:[ Const 2 ] @@ focus_entry empty
  in
  let block_args = Constprop.block_args cfg in
  let cfg, changed = Constprop.constprop block_args cfg in
  (check bool) "Graph changed" changed true;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let test_const_prop_args () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ label (1, "")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (bop Ast.Add ~src1:(Const 1) ~src2:(reg "a") ~dest:(reg "b"))
    @@ branch ~args:[ reg "b"; reg "a" ] (2, "")
    @@ label ~args:[ name "c"; name "d" ] (2, "")
    @@ return ~uses:[ reg "d" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ label (1, "")
    @@ branch (2, "")
    @@ label (2, "")
    @@ return ~uses:[ Const 1 ] @@ focus_entry empty
  in
  let block_args = Constprop.block_args cfg in
  let cfg, changed = Constprop.constprop block_args cfg in
  (check bool) "Graph changed" changed true;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let test_const_prop_branch () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ label (1, "")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (bop Ast.Add ~src1:(Const 1) ~src2:(reg "a") ~dest:(reg "b"))
    @@ cbranch ~ifnot_args:[ Const 1 ]
         ~args:[ reg "b"; reg "a" ]
         LT ~ifso:(2, "") ~ifnot:(3, "")
    @@ label (2, "")
    @@ instruction (call ~dest:(reg "c") (Const 100) [ Const 1 ])
    @@ branch ~args:[ reg "c" ] (3, "")
    @@ label ~args:[ name "d" ] (3, "")
    @@ return ~uses:[ reg "d" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    (* todo: delete empty blocks *)
    @@ label (1, "")
    @@ branch (3, "")
    @@ label (3, "")
    @@ return ~uses:[ Const 1 ] @@ focus_entry empty
  in
  let block_args = Constprop.block_args cfg in
  let cfg, changed = Constprop.constprop block_args cfg in
  (check bool) "Graph changed" changed true;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let _ =
  run "Normalize to zipper cfg"
    [
      ("Tests block args", [ test_case "example 1" `Quick test_block_args ]);
      ( "Tests constant propagation",
        [
          test_case "simple" `Quick test_const_prop_simple;
          test_case "block args" `Quick test_const_prop_args;
          test_case "conditional branch" `Quick test_const_prop_branch;
        ] );
    ]
