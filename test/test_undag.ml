open Alcotest
open Baby_pascal

let test_example_1 () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ instruction (bop Mul ~dest:(reg "d") ~src1:(reg "c") ~src2:(reg "c"))
    @@ instruction (call ~dest:(reg "e") (Label ((100, "f"), [])) [])
    @@ focus_entry empty
  in
  let block = Normalize.Cfg.(zip (fst (focus_entry cfg))) in
  let block = Undag.undag block in
  let expected =
    let open Undag.Target in
    let open Undag.Cfg in
    unfocus
    @@ instruction
         (bop Add ~dest:(reg "c")
            ~src1:(Instr (assign ~src:(Const 1) ~dest:(reg "a")))
            ~src2:(Instr (assign ~src:(Const 2) ~dest:(reg "b"))))
    @@ instruction (bop Mul ~dest:(reg "d") ~src1:(reg "c") ~src2:(reg "c"))
    @@ instruction (call ~dest:(reg "e") (Label ((100, "f"), [])) [])
    @@ focus_entry empty
  in
  let expected = Undag.Cfg.(zip (fst (focus_entry expected))) in
  (check Undag.Cfg.(testable pp_block equal_block))
    "Produces proper graph" expected block

let test_use_in_jump () =
  let cfg =
    let open Normalize.Target in
    let open Normalize.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ instruction (assign ~src:(Const 2) ~dest:(reg "b"))
    @@ instruction (bop Add ~dest:(reg "c") ~src1:(reg "a") ~src2:(reg "b"))
    @@ branch ~args:[ reg "c"; reg "a" ] (1, "label1")
    @@ label (1, "label1")
    @@ exit @@ focus_entry empty
  in
  let block = Normalize.Cfg.(zip (fst (focus_entry cfg))) in
  let block = Undag.undag block in
  let expected =
    let open Undag.Target in
    let open Undag.Cfg in
    unfocus
    @@ instruction (assign ~src:(Const 1) ~dest:(reg "a"))
    @@ branch
         ~args:
           [
             Instr
               (bop Add ~dest:(reg "c") ~src1:(reg "a")
                  ~src2:(Instr (assign ~src:(Const 2) ~dest:(reg "b"))));
             reg "a";
           ]
         (1, "label1")
    @@ label (1, "label1")
    @@ exit @@ focus_entry empty
  in
  let expected = Undag.Cfg.(zip (fst (focus_entry expected))) in
  (check Undag.Cfg.(testable pp_block equal_block))
    "Produces proper graph" expected block

let _ =
  run "Test undag to list of trees"
    [
      ( "Tests proper output",
        [
          test_case "example 1" `Quick test_example_1;
          test_case "second use in jump" `Quick test_use_in_jump;
        ] );
    ]
