open Alcotest
open Baby_pascal.Cfg
open Baby_pascal.Code
open Baby_pascal.Dom
open Baby_pascal.Ssa

module BlockList = struct
  type t = Block.t list [@@deriving show, eq]
end

let test_figure_19_2 () =
  reset ();
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
  let v = sym_to_string |> Hashtbl.to_seq_keys |> S.of_seq in
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
  reset ();
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
  let v = sym_to_string |> Hashtbl.to_seq_keys |> S.of_seq in
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

let _ =
  run "SSA conversion tests"
    [
      ( "Test conversion into SSA",
        [
          test_case "Figure 19.2" `Quick test_figure_19_2;
          test_case "Figure 19.3" `Quick test_figure_19_3;
        ] );
    ]
