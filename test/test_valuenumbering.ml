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
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "c"))
    @@ instruction (assign ~src:(Const 9) ~dest:(reg "e"))
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
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "c"))
    @@ cbranch ~args:[ Const 1; Const 0 ] EQ ~ifso:(1, "label1")
         ~ifnot:(2, "label2")
    @@ label (1, "label1")
    @@ branch (3, "label3")
    @@ label (2, "label2")
    @@ label (3, "label3")
    @@ instruction (assign ~src:(Const 9) ~dest:(reg "f"))
    @@ instruction (assign ~src:(Const 27) ~dest:(reg "g"))
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
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "c"))
    @@ cbranch ~args:[ Const 1; Const 0 ] EQ ~ifso:(2, "label2")
         ~ifnot:(1, "label1")
    @@ label (1, "label1")
    @@ label (2, "label2")
    @@ instruction (assign ~src:(Const 9) ~dest:(reg "e"))
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
    @@ instruction (assign ~src:(Const 3) ~dest:(reg "c"))
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

(* Test (0 + a + 0) | ~((a | (a & b)) & b) -> -1 *)
let test_simplify () =
  (* Test that phis with loop and backedge gets ignored *)
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 0) ~dest:(reg "zero"))
    @@ instruction (call ~dest:(reg "a") (Label ((100, "z"), [])) [])
    @@ instruction (call ~dest:(reg "b") (Label ((100, "z"), [])) [])
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(Const 0) ~src2:(reg "a"))
    @@ instruction (bop Add ~dest:(reg "d") ~src1:(reg "c") ~src2:(reg "zero"))
    @@ instruction (bop And ~dest:(reg "e") ~src1:(reg "a") ~src2:(reg "b"))
    @@ instruction (bop Or ~dest:(reg "f") ~src1:(reg "a") ~src2:(reg "e"))
    @@ instruction (bop And ~dest:(reg "g") ~src1:(reg "f") ~src2:(reg "b"))
    @@ instruction (uop Not ~dest:(reg "h") ~src:(reg "g"))
    @@ instruction (bop Or ~dest:(reg "i") ~src1:(reg "d") ~src2:(reg "h"))
    @@ return ~uses:[ reg "i" ]
    @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (call ~dest:(reg "a") (Label ((100, "z"), [])) [])
    @@ instruction (call ~dest:(reg "b") (Label ((100, "z"), [])) [])
    @@ instruction (assign ~src:(Const (-1)) ~dest:(reg "i"))
    @@ return ~uses:[ reg "i" ]
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let state = Valuenumbering.init_state () in
  let cfg = Valuenumbering.dvnt state (Lazy.force Dom.dominator_tree) cfg in
  let cfg, changed = Deadcode.M.deadcode cfg in
  check bool "Graph changed" true (state.changed && changed);
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
          test_case "instruction gets simplified during value numbering" `Quick
            test_simplify;
        ] );
    ]
