open Alcotest
open Baby_pascal
open Select_x86

let test_print () =
  let open Target in
  let v1 = Virtual { id = 1; reg_class = Int; reg_constr = Any } in
  let v2 = Virtual { id = 2; reg_class = Int; reg_constr = Any } in
  let v3 = Virtual { id = 3; reg_class = Int; reg_constr = Any } in
  let instr =
    Target.instr "addq"
      ~defs:[ Reg (reuse v1 v3) ]
      ~uses:[ Reg v1; Reg (constrained Regs.rax v2) ]
  in
  (check string) "add" (show_instr instr) "addq %3(reuse=%1), %1any, %2(%rax)";
  let v1 = Virtual { id = 1; reg_class = Float; reg_constr = OnStack } in
  let v2 = Virtual { id = 2; reg_class = Float; reg_constr = OnReg } in
  let v3 = Virtual { id = 3; reg_class = Float; reg_constr = OnReg } in
  let instr =
    Target.mov ~dest:(Reg v1)
      ~src:(MemAddr { base = v2; index = v3; scale = 10; displacement = 15 })
  in
  (check string) "mov" (show_instr instr) "movq %1fstack, 15(%2freg,%3freg,10)";
  let v1 = Virtual { id = 1; reg_class = Int; reg_constr = Any } in
  let v2 = Virtual { id = 2; reg_class = Int; reg_constr = Any } in
  let v3 = Virtual { id = 3; reg_class = Int; reg_constr = Any } in
  let v4 = Virtual { id = 4; reg_class = Int; reg_constr = Any } in
  let instr =
    Target.pcopy
      ~dests:[ Reg (constrained Regs.rdi v3); Reg (constrained Regs.rsi v4) ]
      ~srcs:[ Reg v1; Reg v2 ]
  in
  (check string) "pcopy" (show_instr instr)
    "pcopy [(%3(%rdi), %1any); (%4(%rsi), %2any)]"

let _ =
  run "Test undag to list of trees"
    [
      ( "Tests instruction printing",
        [ test_case "instruction" `Quick test_print ] );
    ]
