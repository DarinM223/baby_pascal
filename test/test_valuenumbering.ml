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
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ instruction (bop Mul ~dest:(reg "e") ~src1:(reg "c") ~src2:(reg "c"))
    @@ instruction (call ~dest:(reg "f") (Label ((100, "f"), [])) [])
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Dom = Dominator.Make (Normalize.Cfg) (Extra) in
  let module Valuenumbering = Valuenumbering.Make (Dom) in
  let cfg =
    Valuenumbering.(dvnt (init_state ())) (Lazy.force Dom.dominator_tree) cfg
  in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_phis () =
  (* todo: have block argument with two predecessors with same value number
     also have one with loop and backedge *)
  ()

let _ =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug);
  run "Value numbering"
    [
      ( "Tests proper output",
        [
          test_case "simple" `Quick test_simple;
          test_case "phis" `Quick test_phis;
        ] );
    ]
