open Alcotest
open Baby_pascal
open Baby_pascal.Code
open Baby_pascal.Cfg
open Baby_pascal.Dom
open Baby_pascal.Ssa
open Baby_pascal.Utils

module BlockList = struct
  type t = Block.t list [@@deriving show, eq]
end

module Make () = struct
  module Fresh = Fresh.Make ()
  module Sym = Sym.Make (Fresh)
  include Sym
  include Code.Make (Fresh) (Sym)
  include Ssa.Make (Sym)
end

let test_figure_19_2 () =
  let open Make () in
  let x, a, b, c = (get_sym "x", get_sym "a", get_sym "b", get_sym "c") in
  let block0 =
    CCVector.of_array
      [| (Assign, Name x, Empty, Name b); (Assign, Const 0, Empty, Name a) |]
  in
  let block1 = CCVector.of_array [| (Lt, Name b, Const 4, Const 3) |] in
  let block2 = CCVector.of_array [| (Assign, Name b, Empty, Name a) |] in
  let block3 = CCVector.of_array [| (Add, Name a, Name b, Name c) |] in
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
  insert_phis df a_orig v graph;
  rename v graph;
  let [ x0; a1; a2; a3; b1; c1 ] =
    List.map get_sym [ "x0"; "a1"; "a2"; "a3"; "b1"; "c1" ]
  in
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
              (Assign, Name x0, Empty, Name b1);
              (Assign, Const 0, Empty, Name a1);
            |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 1 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Lt, Name b1, Const 4, Const 3) |];
        pred = S.of_list [ 0 ];
        succ = S.of_list [ 2; 3 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Assign, Name b1, Empty, Name a2) |];
        pred = S.of_list [ 1 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis = CCVector.of_array [| (a3, [ a1; a2 ]) |];
        code = CCVector.of_array [| (Add, Name a3, Name b1, Name c1) |];
        pred = S.of_list [ 1; 2 ];
        succ = S.of_list [ -2 ];
      };
    ]
    (graph |> M.bindings |> List.map snd)

let test_figure_19_3 () =
  let open Make () in
  let a, b, c = (get_sym "a", get_sym "b", get_sym "c") in
  let block0 = CCVector.of_array [| (Assign, Const 0, Empty, Name a) |] in
  let block1 =
    CCVector.of_array
      [|
        (Add, Name a, Const 1, Name b);
        (Add, Name c, Name b, Name c);
        (Mul, Name b, Const 2, Name a);
        (Lt, Name a, Const 10, Const 1);
      |]
  in
  let block2 = CCVector.of_array [| (Return, Name c, Empty, Empty) |] in
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
  insert_phis df a_orig v graph;
  rename v graph;
  let [ a1; a2; a3; b0; b1; b2; c0; c1; c2 ] =
    List.map get_sym [ "a1"; "a2"; "a3"; "b0"; "b1"; "b2"; "c0"; "c1"; "c2" ]
  in
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
        code = CCVector.of_array [| (Assign, Const 0, Empty, Name a1) |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 1 ];
      };
      {
        phis =
          CCVector.of_array
            [| (c1, [ c0; c2 ]); (b1, [ b0; b2 ]); (a2, [ a1; a3 ]) |];
        code =
          CCVector.of_array
            [|
              (Add, Name a2, Const 1, Name b2);
              (Add, Name c2, Name b2, Name c2);
              (Mul, Name b2, Const 2, Name a3);
              (Lt, Name a3, Const 10, Const 1);
            |];
        pred = S.of_list [ 0; 1 ];
        succ = S.of_list [ 1; 2 ];
      };
      {
        phis = CCVector.of_array [||];
        code = CCVector.of_array [| (Return, Name c2, Empty, Empty) |];
        pred = S.of_list [ 1 ];
        succ = S.of_list [ -2 ];
      };
    ]
    (graph |> M.bindings |> List.map snd)

let test_figure_19_4 () =
  let open Make () in
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
        Return (Some (Var "j"));
      ]
  in
  let graph = ast |> normalize |> blocks_of_code in
  let gen_kill_map, instr_of_def = gen_kill graph in
  let v = S.of_seq (syms ()) in
  let a_orig = calc_a_orig gen_kill_map instr_of_def in
  let idom = dominators graph Block.entry in
  let dom_tree = dom_tree_of_idom graph idom in
  let df = dominator_frontier graph dom_tree idom in
  insert_phis df a_orig v graph;
  rename v graph;
  let [ i1; j1; j2; j3; j4; k1; k2; k3; k4 ] =
    List.map get_sym [ "i1"; "j1"; "j2"; "j3"; "j4"; "k1"; "k2"; "k3"; "k4" ]
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
              (Assign, Const 1, Empty, Name i1);
              (Assign, Const 1, Empty, Name j1);
              (Assign, Const 0, Empty, Name k1);
            |];
        pred = S.of_list [ -1 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis =
          CCVector.of_array [| (j2, [ j1; j4; j3 ]); (k2, [ k1; k4; k3 ]) |];
        code = CCVector.of_array [| (Lt, Name k2, Const 100, Const 5) |];
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
        code = CCVector.of_array [| (Lt, Name j2, Const 20, Const 7) |];
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
              (Assign, Name i1, Empty, Name j4);
              (Add, Name k2, Const 1, Temp 3);
              (Assign, Temp 3, Empty, Name k4);
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
              (Assign, Name k2, Empty, Name j3);
              (Add, Name k2, Const 2, Temp 4);
              (Assign, Temp 4, Empty, Name k3);
              (Goto, Const 3, Empty, Empty);
            |];
        pred = S.of_list [ 6 ];
        succ = S.of_list [ 3 ];
      };
      {
        phis = CCVector.of_array [||];
        code =
          CCVector.of_array
            [| (Return, Name j2, Empty, Empty); (Nop, Empty, Empty, Empty) |];
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
