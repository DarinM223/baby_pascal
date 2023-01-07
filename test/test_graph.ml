open Alcotest
open Baby_pascal

module GenKillInfo = struct
  open Cfg

  type t = gen_kill_info M.t

  let pp fmt m =
    Format.fprintf fmt "%s" ([%show: (int * gen_kill_info) list] (M.bindings m))

  let equal = M.equal equal_gen_kill_info
end

let test_figure_9_13 () =
  let open Cfg in
  let a, i, j, m, n, u1, u2, u3 = (1, 2, 3, 4, 5, 6, 7, 8) in
  let example =
    blocks_of_code
      (CCVector.of_array
         Code.
           [|
             (Sub, Name m, Const 1, Name i);
             (Assign, Name n, Empty, Name j);
             (Assign, Name u1, Empty, Name a);
             (Add, Name i, Const 1, Name i);
             (Sub, Name j, Const 1, Name j);
             (Eq, Name j, Const 0, Const 7);
             (Assign, Name u2, Empty, Name a);
             (Assign, Name u3, Empty, Name i);
             (Lt, Name i, Const 5, Const 3);
           |])
  in
  let to_info gen kill gen_block kill_block =
    {
      gen = CCVector.of_array (Array.map S.of_list gen);
      kill = CCVector.of_array (Array.map S.of_list kill);
      gen_block = S.of_list gen_block;
      kill_block = S.of_list kill_block;
    }
  in
  let sets, _ = gen_kill example in
  (check (module GenKillInfo))
    "same gen/kill sets" sets
    (M.of_seq
    @@ List.to_seq
         [
           (-2, to_info [||] [||] [] []);
           (-1, to_info [||] [||] [] []);
           ( 0,
             to_info [| [ 0 ]; [ 1 ]; [ 2 ] |]
               [| [ 3; 6 ]; [ 4 ]; [ 5 ] |]
               [ 0; 1; 2 ] [ 3; 4; 5; 6 ] );
           ( 3,
             to_info [| [ 3 ]; [ 4 ]; [] |]
               [| [ 0; 6 ]; [ 1 ]; [] |]
               [ 3; 4 ] [ 0; 1; 6 ] );
           (6, to_info [| [ 5 ] |] [| [ 2 ] |] [ 5 ] [ 2 ]);
           (7, to_info [| [ 6 ]; [] |] [| [ 0; 3 ]; [] |] [ 6 ] [ 0; 3 ]);
         ])

let _ =
  run "Test control flow graph"
    [
      ( "Tests gen/kill set creation",
        [ test_case "Tests example in figure 9.13" `Quick test_figure_9_13 ] );
    ]
