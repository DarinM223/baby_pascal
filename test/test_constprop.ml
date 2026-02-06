open Alcotest
open Baby_pascal

let test_block_args () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch ~args:[ name "a"; name "b"; name "c" ] (1, "")
    @@ label ~args:[ name "d"; name "e"; name "f" ] (1, "")
    @@ cbranch ~args:[ reg "e"; Const 0 ] EQ ~ifso:(2, "") ~ifnot:(3, "")
    @@ label (2, "")
    @@ branch ~args:[ name "g"; name "h"; name "i" ] (1, "")
    @@ label (3, "")
    @@ exit @@ focus_entry empty
  in
  let expected =
    Constprop.(
      NameMap.of_list
        Normalize.Target.
          [
            (name "d", NameSet.of_list [ name "a"; name "g" ]);
            (name "e", NameSet.of_list [ name "b"; name "h" ]);
            (name "f", NameSet.of_list [ name "c"; name "i" ]);
          ])
  in
  let result = Constprop.block_args cfg in
  (check
     Constprop.(testable (NameMap.pp NameSet.pp) (NameMap.equal NameSet.equal)))
    "Produces proper mapping" result expected

let test_const_prop () = ()

let _ =
  run "Normalize to zipper cfg"
    [
      ("Tests block args", [ test_case "example 1" `Quick test_block_args ]);
      ("Tests constant propagation", [ test_case "" `Quick test_const_prop ]);
    ]
