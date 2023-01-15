open Alcotest
open Baby_pascal.Cfg
open Baby_pascal.Dom

let build_graph nodes edges =
  let graph =
    List.fold_left
      (fun graph n -> M.add n (Block.create (CCVector.create ())) graph)
      M.empty nodes
  in
  let graph =
    List.fold_left
      (fun graph (i, j) ->
        graph
        |> M.update i
             (Option.map (fun node ->
                  Block.{ node with succ = S.add j node.succ }))
        |> M.update j
             (Option.map (fun node ->
                  Block.{ node with pred = S.add i node.pred })))
      graph edges
  in
  graph

let test_figure_18_3 () =
  let nodes = List.init 12 (fun x -> x + 1) in
  let edges =
    [
      (1, 2);
      (2, 3);
      (2, 4);
      (3, 2);
      (4, 2);
      (4, 5);
      (4, 6);
      (5, 7);
      (6, 7);
      (5, 8);
      (7, 11);
      (8, 9);
      (9, 10);
      (10, 12);
      (11, 12);
      (10, 5);
      (9, 8);
    ]
  in
  let graph = build_graph nodes edges in
  let idom = dominators graph 1 in
  let dom_tree = dom_tree_of_idom graph idom in
  let expected_next =
    [
      (1, [ 2 ]);
      (2, [ 3; 4 ]);
      (3, []);
      (4, [ 5; 6; 7; 12 ]);
      (5, [ 8 ]);
      (6, []);
      (7, [ 11 ]);
      (8, [ 9 ]);
      (9, [ 10 ]);
      (10, []);
      (11, []);
      (12, []);
    ]
  in
  M.iter
    (fun n _ ->
      let next = dom_tree n in
      let next' = List.assoc n expected_next in
      let description =
        "Next nodes in dominator tree for node " ^ string_of_int n
      in
      (check (list int)) description (List.sort compare next) next')
    graph

let test_figure_19_5 () =
  let nodes = List.init 13 (fun x -> x + 1) in
  let edges =
    [
      (1, 2);
      (1, 5);
      (1, 9);
      (2, 3);
      (3, 3);
      (3, 4);
      (4, 13);
      (5, 6);
      (5, 7);
      (6, 4);
      (6, 8);
      (7, 12);
      (7, 8);
      (8, 5);
      (8, 13);
      (9, 10);
      (9, 11);
      (10, 12);
      (11, 12);
      (12, 13);
    ]
  in
  let graph = build_graph nodes edges in
  let idom = dominators graph 1 in
  let dom_tree = dom_tree_of_idom graph idom in
  let df = dominator_frontier graph dom_tree idom in
  (check (list int))
    "Dominance frontier for node 5"
    (List.sort compare (df 5))
    [ 4; 5; 12; 13 ]

let _ =
  run "Dominator tree and frontier tests"
    [
      ( "Tests dominator tree",
        [ test_case "Figure 18.3" `Quick test_figure_18_3 ] );
      ( "Tests dominator frontier",
        [ test_case "Figure 19.5" `Quick test_figure_19_5 ] );
    ]
