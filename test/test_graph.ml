open Alcotest
open Baby_pascal

module GenKillInfo = struct
  open Cfg

  type t = (int * gen_kill_info) list [@@deriving show, eq]
end

let test_figure_9_13 () =
  let open Cfg in
  let a, i, j, m, n, u1, u2, u3 = (1, 2, 3, 4, 5, 6, 7, 8) in
  let example =
    blocks_of_code
      (CCVector.of_array
         Code.
           [|
             (Sub, name m, Const 1, name i);
             (Assign, name n, Empty, name j);
             (Assign, name u1, Empty, name a);
             (Add, name i, Const 1, name i);
             (Sub, name j, Const 1, name j);
             (Eq, name j, Const 0, Const 7);
             (Assign, name u2, Empty, name a);
             (Assign, name u3, Empty, name i);
             (Lt, name i, Const 5, Const 3);
           |])
  in
  let sets = gen_kill example in
  (check (module GenKillInfo))
    "same gen/kill sets" (M.bindings sets)
    [
      ( -2,
        {
          gen = CCVector.of_array [||];
          kill = CCVector.of_array [||];
          gen_block = S.of_list [];
          kill_block = S.of_list [];
        } );
      ( -1,
        {
          gen = CCVector.of_array [||];
          kill = CCVector.of_array [||];
          gen_block = S.of_list [];
          kill_block = S.of_list [];
        } );
      ( 0,
        {
          gen =
            CCVector.of_array
              [| S.of_list [ 4 ]; S.of_list [ 5 ]; S.of_list [ 6 ] |];
          kill =
            CCVector.of_array
              [| S.of_list [ 2 ]; S.of_list [ 3 ]; S.of_list [ 1 ] |];
          gen_block = S.of_list [ 4; 5; 6 ];
          kill_block = S.of_list [ 1; 2; 3 ];
        } );
      ( 3,
        {
          gen =
            CCVector.of_array
              [| S.of_list [ 2 ]; S.of_list [ 3 ]; S.of_list [ 3 ] |];
          kill =
            CCVector.of_array
              [| S.of_list [ 2 ]; S.of_list [ 3 ]; S.of_list [] |];
          gen_block = S.of_list [ 2; 3 ];
          kill_block = S.of_list [ 2; 3 ];
        } );
      ( 6,
        {
          gen = CCVector.of_array [| S.of_list [ 7 ] |];
          kill = CCVector.of_array [| S.of_list [ 1 ] |];
          gen_block = S.of_list [ 7 ];
          kill_block = S.of_list [ 1 ];
        } );
      ( 7,
        {
          gen = CCVector.of_array [| S.of_list [ 8 ]; S.of_list [ 2 ] |];
          kill = CCVector.of_array [| S.of_list [ 2 ]; S.of_list [] |];
          gen_block = S.of_list [ 2; 8 ];
          kill_block = S.of_list [ 2 ];
        } );
    ]

let _ =
  run "Test control flow graph"
    [
      ( "Tests gen/kill set creation",
        [ test_case "Tests example in figure 9.13" `Quick test_figure_9_13 ] );
    ]
