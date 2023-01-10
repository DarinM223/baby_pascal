open Alcotest
open Baby_pascal.Code
open Baby_pascal.Cfg
open Baby_pascal.Dom
open Baby_pascal.Ssa

module BlockList = struct
  type t = Block.t list [@@deriving show, eq]
end

let test_figure_19_2 () =
  let open Baby_pascal.Intf.Sym.Make (Baby_pascal.Intf.Fresh.Make ()) in
  let x, a, b, c = (get_sym "x", get_sym "a", get_sym "b", get_sym "c") in
  let block0 =
    CCVector.of_array
      [| (Assign, name x, Empty, name b); (Assign, Const 0, Empty, name a) |]
  in
  let block1 = CCVector.of_array [| (Lt, name b, Const 4, Const 3) |] in
  let block2 = CCVector.of_array [| (Assign, name b, Empty, name a) |] in
  let block3 = CCVector.of_array [| (Add, name a, name b, name c) |] in
  let graph =
    M.of_seq
    @@ List.to_seq
         [
           ( Block.exit,
             Block.{ (create (CCVector.create ())) with pred = S.of_list [ 3 ] }
           );
           ( Block.entry,
             Block.{ (create (CCVector.create ())) with succ = S.of_list [ 0 ] }
           );
           ( 0,
             {
               (Block.create block0) with
               pred = S.of_list [ Block.entry ];
               succ = S.of_list [ 1 ];
             } );
           ( 1,
             {
               (Block.create block1) with
               pred = S.of_list [ 0 ];
               succ = S.of_list [ 2; 3 ];
             } );
           ( 2,
             {
               (Block.create block2) with
               pred = S.of_list [ 1 ];
               succ = S.of_list [ 3 ];
             } );
           ( 3,
             {
               (Block.create block3) with
               pred = S.of_list [ 1; 2 ];
               succ = S.of_list [ Block.exit ];
             } );
         ]
  in
  let gen_kill_map, instr_of_def = gen_kill graph in
  let v = S.of_seq (syms ()) in
  let a_orig = calc_a_orig gen_kill_map instr_of_def in
  let idom = dominators graph Block.entry in
  let dom_tree = dom_tree_of_idom graph idom in
  let df = dominator_frontier graph dom_tree idom in
  insert_phis_minimal df a_orig v graph;
  rename v graph;
  (check (module BlockList))
    "check ssa graph"
    [
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [ 3 ];
        succ = S.of_list [];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [];
        succ = S.of_list [ 0 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [|
              (Assign, Name (x, 0), Empty, Name (b, 1));
              (Assign, Const 0, Empty, Name (a, 1));
            |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 1 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Lt, Name (b, 1), Const 4, Const 3) |];
        pred = S.of_list [ 0 ];
        succ = S.of_list [ 2; 3 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Assign, Name (b, 1), Empty, Name (a, 2)) |];
        pred = S.of_list [ 1 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis =
          CCVector.of_array [| (Name (a, 3), [ Name (a, 1); Name (a, 2) ]) |];
        code =
          CCVector.of_array [| (Add, Name (a, 3), Name (b, 1), Name (c, 1)) |];
        pred = S.of_list [ 1; 2 ];
        succ = S.of_list [ -2 ];
      };
    ]
    (graph |> M.bindings |> List.map snd)

let test_figure_19_3 () =
  let open Baby_pascal.Intf.Sym.Make (Baby_pascal.Intf.Fresh.Make ()) in
  let a, b, c = (get_sym "a", get_sym "b", get_sym "c") in
  let block0 = CCVector.of_array [| (Assign, Const 0, Empty, name a) |] in
  let block1 =
    CCVector.of_array
      [|
        (Add, name a, Const 1, name b);
        (Add, name c, name b, name c);
        (Mul, name b, Const 2, name a);
        (Lt, name a, Const 10, Const 1);
      |]
  in
  let block2 = CCVector.of_array [| (Nop, Empty, Empty, Empty) |] in
  let graph =
    M.of_seq
    @@ List.to_seq
         [
           ( Block.exit,
             Block.{ (create (CCVector.create ())) with pred = S.of_list [ 2 ] }
           );
           ( Block.entry,
             Block.{ (create (CCVector.create ())) with succ = S.of_list [ 0 ] }
           );
           ( 0,
             {
               (Block.create block0) with
               pred = S.of_list [ Block.entry ];
               succ = S.of_list [ 1 ];
             } );
           ( 1,
             {
               (Block.create block1) with
               pred = S.of_list [ 0; 1 ];
               succ = S.of_list [ 1; 2 ];
             } );
           ( 2,
             {
               (Block.create block2) with
               pred = S.of_list [ 1 ];
               succ = S.of_list [ Block.exit ];
             } );
         ]
  in
  let gen_kill_map, instr_of_def = gen_kill graph in
  let v = S.of_seq (syms ()) in
  let a_orig = calc_a_orig gen_kill_map instr_of_def in
  let idom = dominators graph Block.entry in
  let dom_tree = dom_tree_of_idom graph idom in
  let df = dominator_frontier graph dom_tree idom in
  insert_phis_minimal df a_orig v graph;
  rename v graph;
  (check (module BlockList))
    "check ssa graph"
    [
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [ 2 ];
        succ = S.of_list [];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [];
        succ = S.of_list [ 0 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Assign, Const 0, Empty, Name (a, 1)) |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 1 ];
      };
      {
        phis =
          CCVector.of_array
            [|
              (Name (c, 1), [ Name (c, 0); Name (c, 2) ]);
              (Name (b, 1), [ Name (b, 0); Name (b, 2) ]);
              (Name (a, 2), [ Name (a, 1); Name (a, 3) ]);
            |];
        code =
          CCVector.of_array
            [|
              (Add, Name (a, 2), Const 1, Name (b, 2));
              (Add, Name (c, 2), Name (b, 2), Name (c, 2));
              (Mul, Name (b, 2), Const 2, Name (a, 3));
              (Lt, Name (a, 3), Const 10, Const 1);
            |];
        pred = S.of_list [ 0; 1 ];
        succ = S.of_list [ 1; 2 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Nop, Empty, Empty, Empty) |];
        pred = S.of_list [ 1 ];
        succ = S.of_list [ -2 ];
      };
    ]
    (graph |> M.bindings |> List.map snd)

let test_figure_19_4 () =
  let module Fresh = Baby_pascal.Intf.Fresh.Make () in
  let module Sym = Baby_pascal.Intf.Sym.Make (Fresh) in
  let open Sym in
  let open Make (Fresh) (Sym) in
  let ast =
    Baby_pascal.Ast.
      [
        Assign ("i", Int 1);
        Assign ("j", Int 1);
        Assign ("k", Int 0);
        While
          ( Bop (Lt, Var "k", Int 100),
            [
              If
                ( Bop (Lt, Var "j", Int 20),
                  [
                    Assign ("j", Var "i");
                    Assign ("k", Bop (Add, Var "k", Int 1));
                  ],
                  [
                    Assign ("j", Var "k");
                    Assign ("k", Bop (Add, Var "k", Int 2));
                  ] );
            ] );
        Assign ("result", Var "j");
      ]
  in
  let graph = ast |> normalize |> blocks_of_code in
  let gen_kill_map, instr_of_def = gen_kill graph in
  let v = S.of_seq (syms ()) in
  let a_orig = calc_a_orig gen_kill_map instr_of_def in
  let idom = dominators graph Block.entry in
  let dom_tree = dom_tree_of_idom graph idom in
  let df = dominator_frontier graph dom_tree idom in
  insert_phis_minimal df a_orig v graph;
  rename v graph;
  let i, j, k, result =
    (get_sym "i", get_sym "j", get_sym "k", get_sym "result")
  in
  (check (module BlockList))
    "check ssa graph"
    [
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [ 15 ];
        succ = S.of_list [];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [||];
        pred = S.of_list [];
        succ = S.of_list [ 0 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [|
              (Assign, Const 1, Empty, Name (i, 1));
              (Assign, Const 1, Empty, Name (j, 1));
              (Assign, Const 0, Empty, Name (k, 1));
            |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis =
          CCVector.of_array
            [|
              (Name (j, 2), [ Name (j, 1); Name (j, 4); Name (j, 3) ]);
              (Name (k, 2), [ Name (k, 1); Name (k, 4); Name (k, 3) ]);
            |];
        code = CCVector.of_array [| (Lt, Name (k, 2), Const 100, Const 5) |];
        pred = S.of_list [ 0; 7; 11 ];
        succ = S.of_list [ 4; 5 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Goto, Const 15, Empty, Empty) |];
        pred = S.of_list [ 3 ];
        succ = S.of_list [ 15 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Lt, Name (j, 2), Const 20, Const 7) |];
        pred = S.of_list [ 3 ];
        succ = S.of_list [ 6; 7 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Goto, Const 11, Empty, Empty) |];
        pred = S.of_list [ 5 ];
        succ = S.of_list [ 11 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [|
              (Assign, Name (i, 1), Empty, Name (j, 4));
              (Add, Name (k, 2), Const 1, Temp 3);
              (Assign, Temp 3, Empty, Name (k, 4));
              (Goto, Const 3, Empty, Empty);
            |];
        pred = S.of_list [ 5 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [|
              (Assign, Name (k, 2), Empty, Name (j, 3));
              (Add, Name (k, 2), Const 2, Temp 4);
              (Assign, Temp 4, Empty, Name (k, 3));
              (Goto, Const 3, Empty, Empty);
            |];
        pred = S.of_list [ 6 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [|
              (Assign, Name (j, 2), Empty, Name (result, 1));
              (Nop, Empty, Empty, Empty);
            |];
        pred = S.of_list [ 4 ];
        succ = S.of_list [ -2 ];
      };
    ]
    (graph |> M.bindings |> List.map snd)

let _ =
  run "SSA conversion tests"
    [
      ( "Test conversion into SSA",
        [
          test_case "Figure 19.2" `Quick test_figure_19_2;
          test_case "Figure 19.3" `Quick test_figure_19_3;
          test_case "Figure 19.4" `Quick test_figure_19_4;
        ] );
    ]
