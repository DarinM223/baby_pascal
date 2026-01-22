open Alcotest
open Baby_pascal

let name' s i = Normalize.(Name.update_index i (Target.name s))
let reg' s i = Normalize.Target.Reg (name' s i)

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
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ cbranch ~uses:[ name' "i" 0 ] LT ~ifso:(6, "label6") ~ifnot:(7, "label7")
    @@ label (1, "label1")
    @@ exit
    @@ label ~args:[ name' "z" 3 ] (2, "label2")
    @@ instruction (assign ~src:(reg' "z" 3) ~dest:(reg' "result" 1))
    @@ branch (1, "label1")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg' "z" 1))
    @@ branch ~args:[ name' "z" 1 ] (2, "label2")
    @@ label (4, "label4")
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "z" 2))
    @@ branch ~args:[ name' "z" 2 ] (2, "label2")
    @@ label (5, "label5")
    @@ cbranch ~uses:[ name' "i" 0 ] LT ~ifso:(3, "label3") ~ifnot:(4, "label4")
    @@ label (6, "label6")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg' "y" 1))
    @@ branch (5, "label5")
    @@ label (7, "label7")
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "y" 2))
    @@ branch (5, "label5")
    @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let _ =
  run "Test SSA construction for zipper CFG"
    [
      ( "Tests proper output",
        [ test_case "figure 19.4" `Quick test_figure_19_4 ] );
    ]
