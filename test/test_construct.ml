open Alcotest
open Baby_pascal

let test_figure_19_4 () =
  let ast =
    Ast.
      [
        If
          ( Bop (Lt, Var "i", Int 2),
            [ Assign ("y", Int 1) ],
            [ Assign ("y", Var "x") ] );
        If
          ( Bop (Lt, Var "i", Int 2),
            [ Assign ("z", Int 1) ],
            [ Assign ("z", Var "x") ] );
        Assign ("result", Var "z");
      ]
  in
  let cfg = Normalize.normalize ast in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra =
    (val extra
        : Graph.Extra with type graph = Normalize.Cfg.graph
         and type label = Normalize.Target.label)
  in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let a_orig = Construct.calc_a_orig cfg in
  let live = Construct.calc_live cfg in
  let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
  let cfg = Construct.rename_variables (module Dom) cfg in
  let expected = Normalize.Cfg.empty in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let _ =
  run "Test SSA construction for zipper CFG"
    [
      ( "Tests proper output",
        [ test_case "figure 19.4" `Quick test_figure_19_4 ] );
    ]
