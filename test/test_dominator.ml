open Alcotest
open Baby_pascal

let test_dom () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch (2, "")
    @@ label (2, "")
    @@ cbranch ~args:[ reg "a"; Const 2 ] EQ ~ifso:(3, "") ~ifnot:(4, "")
    @@ label (3, "")
    @@ cbranch ~args:[ reg "b"; Const 1 ] EQ ~ifso:(5, "") ~ifnot:(6, "")
    @@ label (4, "")
    @@ return ~uses:[]
    @@ label (5, "")
    @@ branch (7, "")
    @@ label (6, "")
    @@ branch (7, "")
    @@ label (7, "")
    @@ branch (2, "")
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra =
    (val extra
        : Graph.Extra with type graph = Normalize.Cfg.graph
         and type label = Normalize.Target.label)
  in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let tree = Lazy.force Dom.dominator_tree in
  let expected =
    let open Dom in
    Node
      ( 0,
        None,
        [
          Node
            ( 1,
              Some (2, ""),
              [
                Node
                  ( 2,
                    Some (3, ""),
                    [
                      Leaf (3, Some (5, ""));
                      Leaf (3, Some (6, ""));
                      Leaf (3, Some (7, ""));
                    ] );
                Leaf (2, Some (4, ""));
              ] );
        ] )
  in
  (check Dom.(testable pp_tree equal_tree))
    "Produces proper dominator tree" tree expected;
  let tree =
    Lazy.force Dom.dominator_tree_at (Extra.position_of_label (Some (3, "")))
  in
  let expected =
    Dom.(
      Node
        ( 2,
          Some (3, ""),
          [
            Leaf (3, Some (5, ""));
            Leaf (3, Some (6, ""));
            Leaf (3, Some (7, ""));
          ] ))
  in
  (check Dom.(testable pp_tree equal_tree))
    "Produces proper dominator subtree" tree expected;
  (check bool) "Entry dominates middle node"
    (Dom.dominates
       (Extra.position_of_label None)
       (Extra.position_of_label (Some (3, ""))))
    true;
  (check bool) "Middle node dominates leaf node"
    (Dom.dominates
       (Extra.position_of_label (Some (2, "")))
       (Extra.position_of_label (Some (5, ""))))
    true;
  (check bool) "Child doesn't dominate parent"
    (Dom.dominates
       (Extra.position_of_label (Some (5, "")))
       (Extra.position_of_label (Some (3, ""))))
    false;
  (check bool) "Different child doesn't dominate leaf node"
    (Dom.dominates
       (Extra.position_of_label (Some (4, "")))
       (Extra.position_of_label (Some (5, ""))))
    false;
  let df = Lazy.force Dom.dominator_frontier in
  let labels =
    [
      None;
      Some (2, "");
      Some (3, "");
      Some (4, "");
      Some (5, "");
      Some (6, "");
      Some (7, "");
    ]
  in
  let expected =
    [
      [];
      [ Some (2, "") ];
      [ Some (2, "") ];
      [];
      [ Some (7, "") ];
      [ Some (7, "") ];
      [ Some (2, "") ];
    ]
  in
  let pp_optlabel = Format.pp_print_option Extra.pp_label in
  let optlabel = testable pp_optlabel (Option.equal Extra.equal_label) in
  List.iter
    (fun (label, expected) ->
      (check (list optlabel))
        (Format.asprintf "Dominator frontier for label %a" pp_optlabel label)
        (List.map Extra.label_of_position (df (Extra.position_of_label label)))
        expected)
    (List.combine labels expected)

let _ =
  run "Test dominator construction"
    [
      ( "Tests proper output",
        [ test_case "example from cooper's paper" `Quick test_dom ] );
    ]
