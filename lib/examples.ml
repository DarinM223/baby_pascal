open Normalize

open struct
  let name = Target.name
end

let nested_loops_ast =
  let open Ast in
  Group
    [
      Assign ("i", Int 0);
      While
        ( Bop (Lt, Var "i", Int 100),
          Group
            [
              Assign ("j", Var "i");
              While
                ( Bop (Lt, Var "j", Int 100),
                  Group
                    [
                      Assign ("j", Bop (Add, Var "j", Int 1));
                      Assign ("i", Bop (Add, Var "i", Int 1));
                    ] );
            ] );
    ]

(** Normalized form of nested_loops_ast *)
let nested_loops =
  let blocks =
    [
      ( Cfg.Entry,
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Assign
                 ( Normalize.Target.Operand.Reg (name "i"),
                   Normalize.Target.Operand.Const 0 )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((6, "label6"), []), (6, "label6"))) ) );
      ( Cfg.Label ((1, "label1"), { Cfg.local = false; args = [] }),
        Cfg.Last Cfg.Exit );
      ( Cfg.Label ((2, "label2"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.CBranch
             ( Target.Cbranch
                 ( Normalize.Target.Operand.Reg (name "i"),
                   Normalize.Target.Operand.Const 100,
                   LT,
                   (3, "label3"),
                   [],
                   (1, "label1"),
                   [] ),
               (3, "label3"),
               (1, "label1") )) );
      ( Cfg.Label ((3, "label3"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Assign
                 ( Normalize.Target.Operand.Reg (name "j"),
                   Normalize.Target.Operand.Reg (name "i") )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((4, "label4"), []), (4, "label4"))) ) );
      ( Cfg.Label ((4, "label4"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.CBranch
             ( Target.Cbranch
                 ( Normalize.Target.Operand.Reg (name "j"),
                   Normalize.Target.Operand.Const 100,
                   LT,
                   (5, "label5"),
                   [],
                   (2, "label2"),
                   [] ),
               (5, "label5"),
               (2, "label2") )) );
      ( Cfg.Label ((5, "label5"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Bop
                 ( Normalize.Target.Operand.Reg (name "tmp1"),
                   Ast.Add,
                   Normalize.Target.Operand.Reg (name "j"),
                   Normalize.Target.Operand.Const 1 )),
            Cfg.Tail
              ( Cfg.Instruction
                  (Target.Assign
                     ( Normalize.Target.Operand.Reg (name "j"),
                       Normalize.Target.Operand.Reg (name "tmp1") )),
                Cfg.Tail
                  ( Cfg.Instruction
                      (Target.Bop
                         ( Normalize.Target.Operand.Reg (name "tmp0"),
                           Ast.Add,
                           Normalize.Target.Operand.Reg (name "i"),
                           Normalize.Target.Operand.Const 1 )),
                    Cfg.Tail
                      ( Cfg.Instruction
                          (Target.Assign
                             ( Normalize.Target.Operand.Reg (name "i"),
                               Normalize.Target.Operand.Reg (name "tmp0") )),
                        Cfg.Last
                          (Cfg.Branch
                             (Target.Goto ((4, "label4"), []), (4, "label4")))
                      ) ) ) ) );
      ( Cfg.Label ((6, "label6"), { Cfg.local = false; args = [] }),
        Cfg.Last (Cfg.Branch (Target.Goto ((2, "label2"), []), (2, "label2")))
      );
    ]
  in
  List.fold_left (fun acc block -> Cfg.Blocks.insert block acc) Cfg.empty blocks

let fibonacci_ast =
  let fibonacci fn v =
    let open Ast in
    If
      ( Bop (Le, Var v, Int 1),
        Assign (fn, Var v),
        Assign
          ( fn,
            Bop
              ( Add,
                Call (fn, [ Bop (Sub, Var v, Int 1) ]),
                Call (fn, [ Bop (Sub, Var v, Int 2) ]) ) ) )
  in
  fibonacci "fibonacci" "v"

(** Normalized form of fibonacci_ast
    {[
    let module F = Normalize.Fresh () in
    let cfg =
      Normalize.(set_return "fibonacci" (normalize F.fresh fibonacci_ast))
    in
    cfg
    ]} *)
let fibonacci =
  let blocks =
    [
      ( Cfg.Entry,
        Cfg.Last
          (Cfg.CBranch
             ( Target.Cbranch
                 ( Target.Operand.Reg (name "v"),
                   Target.Operand.Const 1,
                   LE,
                   (2, "label2"),
                   [],
                   (3, "label3"),
                   [] ),
               (2, "label2"),
               (3, "label3") )) );
      ( Cfg.Label ((1, "label1"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.Return (Target.Return [ Target.Operand.Reg (name "fibonacci") ]))
      );
      ( Cfg.Label ((2, "label2"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Assign
                 ( Target.Operand.Reg (name "fibonacci"),
                   Target.Operand.Reg (name "v") )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((1, "label1"), []), (1, "label1"))) ) );
      ( Cfg.Label ((3, "label3"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Bop
                 ( Target.Operand.Reg (name "tmp0"),
                   Ast.Sub,
                   Target.Operand.Reg (name "v"),
                   Target.Operand.Const 1 )),
            Cfg.Tail
              ( Cfg.Instruction
                  (Target.Call
                     ( Target.Operand.Reg (name "tmp1"),
                       Target.Operand.Label ((-1, "fibonacci"), []),
                       [ Target.Operand.Reg (name "tmp0") ] )),
                Cfg.Tail
                  ( Cfg.Instruction
                      (Target.Bop
                         ( Target.Operand.Reg (name "tmp2"),
                           Ast.Sub,
                           Target.Operand.Reg (name "v"),
                           Target.Operand.Const 2 )),
                    Cfg.Tail
                      ( Cfg.Instruction
                          (Target.Call
                             ( Target.Operand.Reg (name "tmp3"),
                               Target.Operand.Label ((-1, "fibonacci"), []),
                               [ Target.Operand.Reg (name "tmp2") ] )),
                        Cfg.Tail
                          ( Cfg.Instruction
                              (Target.Bop
                                 ( Target.Operand.Reg (name "tmp4"),
                                   Ast.Add,
                                   Target.Operand.Reg (name "tmp1"),
                                   Target.Operand.Reg (name "tmp3") )),
                            Cfg.Tail
                              ( Cfg.Instruction
                                  (Target.Assign
                                     ( Target.Operand.Reg (name "fibonacci"),
                                       Target.Operand.Reg (name "tmp4") )),
                                Cfg.Last
                                  (Cfg.Branch
                                     ( Target.Goto ((1, "label1"), []),
                                       (1, "label1") )) ) ) ) ) ) ) );
    ]
  in
  List.fold_left (fun acc block -> Cfg.Blocks.insert block acc) Cfg.empty blocks
