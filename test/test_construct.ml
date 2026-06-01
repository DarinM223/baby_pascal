open Alcotest
open Baby_pascal

let name' s i = Normalize.(Name.update_index i (Target.name s))
let reg' s i = Normalize.Target.Reg (name' s i)

let test_figure_19_2 () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch (1, "label1")
    @@ label (1, "label1")
    @@ instruction (assign ~src:(reg "x") ~dest:(reg "b"))
    @@ instruction (assign ~src:(Const 0) ~dest:(reg "a"))
    @@ branch (2, "label2")
    @@ label (2, "label2")
    @@ cbranch ~ifnot_args:[ tombstone ]
         ~args:[ reg "b"; Const 4 ]
         LT ~ifso:(3, "label3") ~ifnot:(4, "label4")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(reg "b") ~dest:(reg "a"))
    @@ branch ~args:[ tombstone ] (4, "label4")
    @@ label ~args:[ Normalize.Name.tombstone ] (4, "label4")
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch (5, "label5")
    @@ label (5, "label5")
    @@ exit @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let a_orig = Construct.calc_a_orig cfg in
  let cfg = Construct.insert_phis_minimal (module Dom) a_orig cfg in
  let cfg = Construct.rename_variables (module Dom) cfg in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch (1, "label1")
    @@ label (1, "label1")
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "b" 1))
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch (2, "label2")
    @@ label (2, "label2")
    @@ cbranch
         ~ifnot_args:[ reg' "a" 1 ]
         ~args:[ reg' "b" 1; Const 4 ]
         LT ~ifso:(3, "label3") ~ifnot:(4, "label4")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(reg' "b" 1) ~dest:(reg' "a" 2))
    @@ branch ~args:[ reg' "a" 2 ] (4, "label4")
    @@ label ~args:[ name' "a" 3 ] (4, "label4")
    @@ instruction
         (bop Add ~dest:(reg' "c" 1) ~src1:(reg' "a" 3) ~src2:(reg' "b" 1))
    @@ branch (5, "label5")
    @@ label (5, "label5")
    @@ exit @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let test_figure_19_3 () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch (1, "label1")
    @@ label (1, "label1")
    @@ instruction (assign ~src:(Const 0) ~dest:(reg "a"))
    @@ branch (2, "label2")
    @@ label (2, "label2")
    @@ instruction (bop Add ~dest:(reg "b") ~src1:(reg "a") ~src2:(Const 1))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "c") ~src2:(reg "b"))
    @@ instruction (bop Mul ~dest:(reg "a") ~src1:(reg "b") ~src2:(Const 2))
    @@ cbranch
         ~args:[ reg "a"; Const 10 ]
         LT ~ifso:(2, "label2") ~ifnot:(3, "label3")
    @@ label (3, "label3")
    @@ exit @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let a_orig = Construct.calc_a_orig cfg in
  let cfg = Construct.insert_phis_minimal (module Dom) a_orig cfg in
  let cfg = Construct.rename_variables (module Dom) cfg in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ branch (1, "label1")
    @@ label (1, "label1")
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch ~args:[ reg' "c" 0; reg' "b" 0; reg' "a" 1 ] (2, "label2")
    @@ label ~args:[ name' "c" 1; name' "b" 1; name' "a" 2 ] (2, "label2")
    @@ instruction
         (bop Add ~dest:(reg' "b" 2) ~src1:(reg' "a" 2) ~src2:(Const 1))
    @@ instruction
         (bop Add ~dest:(reg' "c" 2) ~src1:(reg' "c" 1) ~src2:(reg' "b" 2))
    @@ instruction
         (bop Mul ~dest:(reg' "a" 3) ~src1:(reg' "b" 2) ~src2:(Const 2))
    @@ cbranch
         ~ifso_args:[ reg' "c" 2; reg' "b" 2; reg' "a" 3 ]
         ~args:[ reg' "a" 3; Const 10 ]
         LT ~ifso:(2, "label2") ~ifnot:(3, "label3")
    @@ label (3, "label3")
    @@ exit @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let test_figure_19_4 () =
  let ast =
    Ast.
      [
        Assign ("i", Int 1);
        Assign ("j", Int 1);
        Assign ("k", Int 0);
        While
          ( Bop (Lt, Var "k", Int 100),
            If
              ( Bop (Lt, Var "j", Int 20),
                Group
                  [
                    Assign ("j", Var "i");
                    Assign ("k", Bop (Add, Var "k", Int 1));
                  ],
                Group
                  [
                    Assign ("j", Var "k");
                    Assign ("k", Bop (Add, Var "k", Int 2));
                  ] ) );
        Assign ("result", Var "j");
      ]
  in
  let module Fresh = Normalize.Fresh () in
  let cfg = Normalize.normalize Fresh.fresh ast in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let a_orig = Construct.calc_a_orig cfg in
  let live = Construct.calc_live cfg in
  let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
  let cfg = Construct.rename_variables (module Dom) cfg in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg' "i" 1))
    @@ branch (9, "label9")
    @@ label (1, "label1")
    @@ exit
    @@ label (2, "label2")
    @@ instruction (assign ~src:(reg' "j" 2) ~dest:(reg' "result" 1))
    @@ branch (1, "label1")
    @@ label ~args:[ name' "k" 2; name' "j" 2 ] (3, "label3")
    @@ cbranch
         ~args:[ reg' "k" 2; Const 100 ]
         LT ~ifso:(4, "label4") ~ifnot:(2, "label2")
    @@ label (4, "label4")
    @@ cbranch
         ~args:[ reg' "j" 2; Const 20 ]
         LT ~ifso:(5, "label5") ~ifnot:(6, "label6")
    @@ label (5, "label5")
    @@ instruction (assign ~src:(reg' "i" 1) ~dest:(reg' "j" 3))
    @@ instruction
         (bop Add ~dest:(reg' "tmp1" 1) ~src1:(reg' "k" 2) ~src2:(Const 1))
    @@ instruction (assign ~src:(reg' "tmp1" 1) ~dest:(reg' "k" 3))
    @@ branch ~args:[ reg' "k" 3; reg' "j" 3 ] (3, "label3")
    @@ label (6, "label6")
    @@ instruction (assign ~src:(reg' "k" 2) ~dest:(reg' "j" 4))
    @@ instruction
         (bop Add ~dest:(reg' "tmp0" 1) ~src1:(reg' "k" 2) ~src2:(Const 2))
    @@ instruction (assign ~src:(reg' "tmp0" 1) ~dest:(reg' "k" 4))
    @@ branch ~args:[ reg' "k" 4; reg' "j" 4 ] (3, "label3")
    @@ label (7, "label7")
    @@ branch ~args:[ reg' "k" 1; reg' "j" 1 ] (3, "label3")
    @@ label (8, "label8")
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "k" 1))
    @@ branch (7, "label7")
    @@ label (9, "label9")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg' "j" 1))
    @@ branch (8, "label8")
    @@ focus_entry empty
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let test_pruned () =
  let ast =
    Ast.
      [
        If (Bop (Lt, Var "i", Int 2), Assign ("y", Int 1), Assign ("y", Var "x"));
        If (Bop (Lt, Var "i", Int 2), Assign ("z", Int 1), Assign ("z", Var "x"));
        Assign ("result", Var "z");
      ]
  in
  let module Fresh = Normalize.Fresh () in
  let cfg = Normalize.normalize Fresh.fresh ast in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let a_orig = Construct.calc_a_orig cfg in
  let live = Construct.calc_live cfg in
  let cfg = Construct.insert_phis_pruned live (module Dom) a_orig cfg in
  let cfg = Construct.rename_variables (module Dom) cfg in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ cbranch
         ~args:[ reg' "i" 0; Const 2 ]
         LT ~ifso:(6, "label6") ~ifnot:(7, "label7")
    @@ label (1, "label1")
    @@ exit
    @@ label ~args:[ name' "z" 3 ] (2, "label2")
    @@ instruction (assign ~src:(reg' "z" 3) ~dest:(reg' "result" 1))
    @@ branch (1, "label1")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(Const 1) ~dest:(reg' "z" 1))
    @@ branch ~args:[ reg' "z" 1 ] (2, "label2")
    @@ label (4, "label4")
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "z" 2))
    @@ branch ~args:[ reg' "z" 2 ] (2, "label2")
    @@ label (5, "label5")
    @@ cbranch
         ~args:[ reg' "i" 0; Const 2 ]
         LT ~ifso:(3, "label3") ~ifnot:(4, "label4")
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
        [
          test_case "figure 19.2" `Quick test_figure_19_2;
          test_case "figure 19.3" `Quick test_figure_19_3;
          test_case "figure 19.4" `Quick test_figure_19_4;
          test_case "pruned" `Quick test_pruned;
        ] );
    ]
