open Alcotest
open Baby_pascal

let test_simple_x86 () =
  let module Sequentialize = Seqpcopy.Make (X86.Cfg) (X86.SeqpcopyRequirements)
  in
  let reg1 =
    X86.Target.Reg
      (Virtual
         {
           id = 1;
           reg_class = Int;
           reg_constr = OnStack;
           reg = Physical X86.Regs.rax;
         })
  in
  let reg2 =
    X86.Target.Reg
      (Virtual
         {
           id = 1;
           reg_class = Int;
           reg_constr = OnStack;
           reg = Physical X86.Regs.rbx;
         })
  in
  let cfg =
    let open X86.Cfg in
    let open X86.Target in
    unfocus
    @@ instruction (pcopy ~dests:[ reg1; reg2 ] ~srcs:[ reg2; reg1 ])
    @@ instruction (pcopy ~dests:[ reg2; reg1 ] ~srcs:[ reg1; reg2 ])
    @@ instruction (pcopy ~dests:[ reg1; reg2 ] ~srcs:[ reg1; reg2 ])
    @@ focus_entry empty
  in
  let cfg = Sequentialize.sequentialize cfg in
  let temp = X86.SeqpcopyRequirements.temp in
  let expected =
    let open X86.Cfg in
    let open X86.Target in
    unfocus
    @@ instruction (mov ~dest:temp ~src:(to_colored reg2))
    @@ instruction (mov ~dest:(to_colored reg2) ~src:(to_colored reg1))
    @@ instruction (mov ~dest:(to_colored reg1) ~src:temp)
    @@ instruction (mov ~dest:temp ~src:(to_colored reg1))
    @@ instruction (mov ~dest:(to_colored reg1) ~src:(to_colored reg2))
    @@ instruction (mov ~dest:(to_colored reg2) ~src:temp)
    @@ focus_entry empty
  in
  (check X86.Cfg.(testable pp_graph equal_graph))
    "Produces proper graph" cfg expected

let _ =
  run "Test sequentializing parallel copies"
    [
      ( "Tests sequentializing parallel copies for X86",
        [ test_case "simple example" `Quick test_simple_x86 ] );
    ]
