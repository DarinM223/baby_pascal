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

let test_const_prop () = ()

let _ =
  run "Normalize to zipper cfg"
    [
      ("Tests block args", [ test_case "example 1" `Quick test_block_args ]);
      ("Tests constant propagation", [ test_case "" `Quick test_const_prop ]);
    ]
