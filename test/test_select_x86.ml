open Alcotest
open Baby_pascal

let test_print () =
  let open X86 in
  let open Target in
  let new_reg vreg =
    let rec reg = Virtual { vreg with reg } in
    reg
  in
  let reg = Tombstone in
  let v1 = new_reg { id = 1; reg_class = Int; reg_constr = Any; reg } in
  let v2 = new_reg { id = 2; reg_class = Int; reg_constr = Any; reg } in
  let v3 = new_reg { id = 3; reg_class = Int; reg_constr = Any; reg } in
  let instr =
    instr "addq"
      ~defs:[ Reg (reuse v1 v3) ]
      ~uses:[ Reg v1; Reg (constrained Regs.rax v2) ]
  in
  (check string) "add" "addq %3(reuse=%1), %1any, %2(%rax)" (show_instr instr);
  let v1 = new_reg { id = 1; reg_class = Float; reg_constr = OnStack; reg } in
  let v2 = new_reg { id = 2; reg_class = Float; reg_constr = OnReg; reg } in
  let v3 = new_reg { id = 3; reg_class = Float; reg_constr = OnReg; reg } in
  let instr =
    mov ~dest:(Reg v1)
      ~src:(MemAddr { base = v2; index = v3; scale = 10; displacement = 15 })
  in
  (check string) "mov" "movq %1fstack, 15(%2freg,%3freg,10)" (show_instr instr);
  let v1 = new_reg { id = 1; reg_class = Int; reg_constr = Any; reg } in
  let v2 = new_reg { id = 2; reg_class = Int; reg_constr = Any; reg } in
  let v3 = new_reg { id = 3; reg_class = Int; reg_constr = Any; reg } in
  let v4 = new_reg { id = 4; reg_class = Int; reg_constr = Any; reg } in
  let instr =
    pcopy
      ~dests:[ Reg (constrained Regs.rdi v3); Reg (constrained Regs.rsi v4) ]
      ~srcs:[ Reg v1; Reg v2 ]
  in
  (check string) "pcopy" "pcopy [(%3(%rdi), %1any); (%4(%rsi), %2any)]"
    (show_instr instr)

let _ =
  run "Test undag to list of trees"
    [
      ( "Tests instruction printing",
        [ test_case "instruction" `Quick test_print ] );
    ]
