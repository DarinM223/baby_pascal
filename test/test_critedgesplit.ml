open Alcotest
open Baby_pascal

let name' s i = Normalize.(Name.update_index i (Target.name s))
let reg' s i = Normalize.Target.Reg (name' s i)

let test_figure_19_2 () =
  let module Fresh = Normalize.Fresh () in
  let label1 = Fresh.new_label () in
  let label2 = Fresh.new_label () in
  let label3 = Fresh.new_label () in
  let label4 = Fresh.new_label () in
  let label5 = Fresh.new_label () in
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus @@ branch label1 @@ label label1
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "b" 1))
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch label2 @@ label label2
    @@ cbranch
         ~ifnot_args:[ reg' "a" 1 ]
         ~args:[ reg' "b" 1; Const 4 ]
         LT ~ifso:label3 ~ifnot:label4
    @@ label label3
    @@ instruction (assign ~src:(reg' "b" 1) ~dest:(reg' "a" 2))
    @@ branch ~args:[ reg' "a" 2 ] label4
    @@ label ~args:[ name' "a" 3 ] label4
    @@ instruction
         (bop Add ~dest:(reg' "c" 1) ~src1:(reg' "a" 3) ~src2:(reg' "b" 1))
    @@ branch label5 @@ label label5 @@ exit @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus @@ branch label1 @@ label label1
    @@ instruction (assign ~src:(reg' "x" 0) ~dest:(reg' "b" 1))
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch label2 @@ label label2
    @@ cbranch ~args:[ reg' "b" 1; Const 4 ] LT ~ifso:label3 ~ifnot:(6, "label6")
    @@ label label3
    @@ instruction (assign ~src:(reg' "b" 1) ~dest:(reg' "a" 2))
    @@ branch ~args:[ reg' "a" 2 ] label4
    @@ label ~args:[ name' "a" 3 ] label4
    @@ instruction
         (bop Add ~dest:(reg' "c" 1) ~src1:(reg' "a" 3) ~src2:(reg' "b" 1))
    @@ branch label5 @@ label label5 @@ exit
    @@ label (6, "label6")
    @@ branch ~args:[ reg' "a" 1 ] label4
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Critedgesplit =
    Critedgesplit.Make (Fresh) (Normalize.Cfg) (Extra)
      (struct
        module Target = Normalize.Target
        include Target
      end) in
  let cfg = Critedgesplit.split cfg in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let test_figure_19_3 () =
  let module Fresh = Normalize.Fresh () in
  let label1 = Fresh.new_label () in
  let label2 = Fresh.new_label () in
  let label3 = Fresh.new_label () in
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus @@ branch label1 @@ label label1
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch ~args:[ reg' "c" 0; reg' "b" 0; reg' "a" 1 ] label2
    @@ label ~args:[ name' "c" 1; name' "b" 1; name' "a" 2 ] label2
    @@ instruction
         (bop Add ~dest:(reg' "b" 2) ~src1:(reg' "a" 2) ~src2:(Const 1))
    @@ instruction
         (bop Add ~dest:(reg' "c" 2) ~src1:(reg' "c" 1) ~src2:(reg' "b" 2))
    @@ instruction
         (bop Mul ~dest:(reg' "a" 3) ~src1:(reg' "b" 2) ~src2:(Const 2))
    @@ cbranch
         ~ifso_args:[ reg' "c" 2; reg' "b" 2; reg' "a" 3 ]
         ~args:[ reg' "a" 3; Const 10 ]
         LT ~ifso:label2 ~ifnot:label3
    @@ label label3 @@ exit @@ focus_entry empty
  in
  let expected =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus @@ branch label1 @@ label label1
    @@ instruction (assign ~src:(Const 0) ~dest:(reg' "a" 1))
    @@ branch ~args:[ reg' "c" 0; reg' "b" 0; reg' "a" 1 ] label2
    @@ label ~args:[ name' "c" 1; name' "b" 1; name' "a" 2 ] label2
    @@ instruction
         (bop Add ~dest:(reg' "b" 2) ~src1:(reg' "a" 2) ~src2:(Const 1))
    @@ instruction
         (bop Add ~dest:(reg' "c" 2) ~src1:(reg' "c" 1) ~src2:(reg' "b" 2))
    @@ instruction
         (bop Mul ~dest:(reg' "a" 3) ~src1:(reg' "b" 2) ~src2:(Const 2))
    @@ cbranch
         ~args:[ reg' "a" 3; Const 10 ]
         LT ~ifso:(4, "label4") ~ifnot:label3
    @@ label label3 @@ exit
    @@ label (4, "label4")
    @@ branch ~args:[ reg' "c" 2; reg' "b" 2; reg' "a" 3 ] label2
    @@ focus_entry empty
  in
  let extra = Normalize.Cfg.precalculate_edges cfg in
  let module Extra = (val extra) in
  let module Critedgesplit =
    Critedgesplit.Make (Fresh) (Normalize.Cfg) (Extra)
      (struct
        module Target = Normalize.Target
        include Target
      end) in
  let cfg = Critedgesplit.split cfg in
  (check Normalize.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" expected cfg

let _ =
  run "Test critical edge splitting"
    [
      ( "Tests proper output",
        [
          test_case "figure 19.2" `Quick test_figure_19_2;
          test_case "figure 19.3" `Quick test_figure_19_3;
        ] );
    ]
