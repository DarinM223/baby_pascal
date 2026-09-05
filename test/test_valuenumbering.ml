open Alcotest
open Baby_pascal

let test_simple () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "a") ~src2:(reg "b"))
    @@ instruction (bop Mul ~dest:(reg "e") ~src1:(reg "c") ~src2:(reg "d"))
    @@ instruction (call ~dest:(reg "f") (Label ((100, "f"), [])) [])
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(Const 1) ~src2:(Const 2))
    @@ instruction (bop Mul ~dest:(reg "e") ~src1:(reg "c") ~src2:(reg "c"))
    @@ instruction (call ~dest:(reg "f") (Label ((100, "f"), [])) [])
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let state = Valuenumbering.init_state () in
  let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
  check bool "Graph changed" true state.changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_phis () =
  (* Test block argument with two predecessors with same value number *)
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ cbranch
         ~args:[ reg "a"; Const 0 ]
         EQ ~ifso:(1, "label1") ~ifnot:(2, "label2")
    @@ label (1, "label1")
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "d" ] (3, "label3")
    @@ label (2, "label2")
    @@ instruction (bop Add ~dest:(reg "e") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "e" ] (3, "label3")
    @@ label ~args:[ name "z" ] (3, "label3")
    @@ instruction (bop Mul ~dest:(reg "f") ~src1:(reg "d") ~src2:(reg "e"))
    @@ instruction (bop Mul ~dest:(reg "g") ~src1:(reg "f") ~src2:(reg "z"))
    @@ instruction (call ~dest:(reg "h") (Label ((100, "func"), [])) [])
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(Const 1) ~src2:(Const 2))
    @@ cbranch ~args:[ Const 1; Const 0 ] EQ ~ifso:(1, "label1")
         ~ifnot:(2, "label2")
    @@ label (1, "label1")
    @@ branch (3, "label3")
    @@ label (2, "label2")
    @@ label (3, "label3")
    @@ instruction (bop Mul ~dest:(reg "f") ~src1:(reg "c") ~src2:(reg "c"))
    @@ instruction (bop Mul ~dest:(reg "g") ~src1:(reg "f") ~src2:(reg "c"))
    @@ instruction (call ~dest:(reg "h") (Label ((100, "func"), [])) [])
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let state = Valuenumbering.init_state () in
  let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
  check bool "Graph changed" true state.changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_phis_reverse_postorder () =
  (* Test that block children are processed in reverse postorder for phis *)
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ cbranch
         ~ifso_args:[ reg "c" ]
         ~args:[ reg "a"; Const 0 ]
         EQ ~ifso:(2, "label2") ~ifnot:(1, "label1")
    @@ label (1, "label1")
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "d" ] (2, "label2")
    @@ label ~args:[ name "z" ] (2, "label2")
    @@ instruction (bop Mul ~dest:(reg "e") ~src1:(reg "z") ~src2:(reg "z"))
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(Const 1) ~src2:(Const 2))
    @@ cbranch ~args:[ Const 1; Const 0 ] EQ ~ifso:(2, "label2")
         ~ifnot:(1, "label1")
    @@ label (1, "label1")
    @@ label (2, "label2")
    @@ instruction (bop Mul ~dest:(reg "e") ~src1:(reg "c") ~src2:(reg "c"))
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let state = Valuenumbering.init_state () in
  let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
  check bool "Graph changed" true state.changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_loop_backedge () =
  (* Test that phis with loop and backedge gets ignored *)
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "c" ] (1, "label1")
    @@ label ~args:[ name "z" ] (1, "label1")
    @@ cbranch
         ~args:[ reg "z"; Const 0 ]
         EQ ~ifso:(3, "label3") ~ifnot:(2, "label2")
    @@ label (2, "label2")
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "d" ] (1, "label1")
    @@ label (3, "label3")
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(Const 1) ~src2:(Const 2))
    @@ branch ~args:[ reg "c" ] (1, "label1")
    @@ label ~args:[ name "z" ] (1, "label1")
    @@ cbranch
         ~args:[ reg "z"; Const 0 ]
         EQ ~ifso:(3, "label3") ~ifnot:(2, "label2")
    @@ label (2, "label2")
    @@ branch ~args:[ reg "c" ] (1, "label1")
    @@ label (3, "label3")
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let state = Valuenumbering.init_state () in
  let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
  check bool "Graph changed" true state.changed;
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Value numbering"
    [
      ( "Tests proper output",
        [
          test_case "simple" `Quick test_simple;
          test_case "simple removal of phis" `Quick test_phis;
          test_case "phi with backedge gets ignored" `Quick test_loop_backedge;
          test_case "block children get processed in reverse postorder" `Quick
            test_phis_reverse_postorder;
        ] );
    ]
