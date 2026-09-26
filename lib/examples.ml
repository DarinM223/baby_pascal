open Normalize

open struct
  let name = Target.name
  let reg = Target.reg TInteger
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
                 ( Normalize.Target.Operand.Reg (TInteger, name "i"),
                   Normalize.Target.Operand.Const 0 )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((6, "label6"), []), (6, "label6"))) ) );
      ( Cfg.Label ((1, "label1"), { Cfg.local = false; args = [] }),
        Cfg.Last Cfg.Exit );
      ( Cfg.Label ((2, "label2"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.CBranch
             ( Target.Cbranch
                 ( Normalize.Target.Operand.Reg (TInteger, name "i"),
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
                 ( Normalize.Target.Operand.Reg (TInteger, name "j"),
                   Normalize.Target.Operand.Reg (TInteger, name "i") )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((4, "label4"), []), (4, "label4"))) ) );
      ( Cfg.Label ((4, "label4"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.CBranch
             ( Target.Cbranch
                 ( Normalize.Target.Operand.Reg (TInteger, name "j"),
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
                 ( Normalize.Target.Operand.Reg (TInteger, name "tmp1"),
                   Ast.Add,
                   Normalize.Target.Operand.Reg (TInteger, name "j"),
                   Normalize.Target.Operand.Const 1 )),
            Cfg.Tail
              ( Cfg.Instruction
                  (Target.Assign
                     ( Normalize.Target.Operand.Reg (TInteger, name "j"),
                       Normalize.Target.Operand.Reg (TInteger, name "tmp1") )),
                Cfg.Tail
                  ( Cfg.Instruction
                      (Target.Bop
                         ( Normalize.Target.Operand.Reg (TInteger, name "tmp0"),
                           Ast.Add,
                           Normalize.Target.Operand.Reg (TInteger, name "i"),
                           Normalize.Target.Operand.Const 1 )),
                    Cfg.Tail
                      ( Cfg.Instruction
                          (Target.Assign
                             ( Normalize.Target.Operand.Reg (TInteger, name "i"),
                               Normalize.Target.Operand.Reg
                                 (TInteger, name "tmp0") )),
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

let cbranch_same_label =
  let name s = (Ast.TInteger, name s) in
  let blocks =
    [
      ( Cfg.Entry,
        Cfg.Tail
          ( Cfg.Instruction (Target.assign ~dest:(reg "a") ~src:(Const 0)),
            Cfg.Tail
              ( Cfg.Instruction (Target.assign ~dest:(reg "b") ~src:(Const 1)),
                Cfg.Tail
                  ( Cfg.Instruction
                      (Target.assign ~dest:(reg "c") ~src:(Const 2)),
                    Cfg.Tail
                      ( Cfg.Instruction
                          (Target.assign ~dest:(reg "d") ~src:(Const 3)),
                        Cfg.Last
                          (Cfg.Branch
                             (Target.Goto ((1, "label1"), []), (1, "label1")))
                      ) ) ) ) );
      ( Cfg.Label ((1, "label1"), { Cfg.local = false; args = [] }),
        Cfg.Last
          (Cfg.CBranch
             ( Target.cbranch
                 ~args:[ reg "a"; reg "b" ]
                 Graph.Cond.EQ (2, "label2")
                 [ Const 1; reg "b"; reg "c" ]
                 (2, "label2")
                 [ reg "a"; Const 2; reg "d" ],
               (2, "label2"),
               (2, "label2") )) );
      ( Cfg.Label
          ( (2, "label2"),
            { Cfg.local = false; args = [ name "e"; name "f"; name "g" ] } ),
        Cfg.Last Cfg.Exit );
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
                 ( Target.Operand.Reg (TInteger, name "v"),
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
          (Cfg.Return
             (Target.Return [ Target.Operand.Reg (TInteger, name "fibonacci") ]))
      );
      ( Cfg.Label ((2, "label2"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Assign
                 ( Target.Operand.Reg (TInteger, name "fibonacci"),
                   Target.Operand.Reg (TInteger, name "v") )),
            Cfg.Last
              (Cfg.Branch (Target.Goto ((1, "label1"), []), (1, "label1"))) ) );
      ( Cfg.Label ((3, "label3"), { Cfg.local = false; args = [] }),
        Cfg.Tail
          ( Cfg.Instruction
              (Target.Bop
                 ( Target.Operand.Reg (TInteger, name "tmp0"),
                   Ast.Sub,
                   Target.Operand.Reg (TInteger, name "v"),
                   Target.Operand.Const 1 )),
            Cfg.Tail
              ( Cfg.Instruction
                  (Target.Call
                     ( Target.Operand.Reg (TInteger, name "tmp1"),
                       Target.Operand.Label ((-1, "fibonacci"), []),
                       [ Target.Operand.Reg (TInteger, name "tmp0") ] )),
                Cfg.Tail
                  ( Cfg.Instruction
                      (Target.Bop
                         ( Target.Operand.Reg (TInteger, name "tmp2"),
                           Ast.Sub,
                           Target.Operand.Reg (TInteger, name "v"),
                           Target.Operand.Const 2 )),
                    Cfg.Tail
                      ( Cfg.Instruction
                          (Target.Call
                             ( Target.Operand.Reg (TInteger, name "tmp3"),
                               Target.Operand.Label ((-1, "fibonacci"), []),
                               [ Target.Operand.Reg (TInteger, name "tmp2") ] )),
                        Cfg.Tail
                          ( Cfg.Instruction
                              (Target.Bop
                                 ( Target.Operand.Reg (TInteger, name "tmp4"),
                                   Ast.Add,
                                   Target.Operand.Reg (TInteger, name "tmp1"),
                                   Target.Operand.Reg (TInteger, name "tmp3") )),
                            Cfg.Tail
                              ( Cfg.Instruction
                                  (Target.Assign
                                     ( Target.Operand.Reg
                                         (TInteger, name "fibonacci"),
                                       Target.Operand.Reg (TInteger, name "tmp4")
                                     )),
                                Cfg.Last
                                  (Cfg.Branch
                                     ( Target.Goto ((1, "label1"), []),
                                       (1, "label1") )) ) ) ) ) ) ) );
    ]
  in
  List.fold_left (fun acc block -> Cfg.Blocks.insert block acc) Cfg.empty blocks
