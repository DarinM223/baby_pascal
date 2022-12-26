open Alcotest
open Baby_pascal

module QuadArray = struct
  type t = Code.quad array [@@deriving show, eq]
end

module BlockList = struct
  type t = Cfg.Block.t list [@@deriving show, eq]
end

let test_example_1 () =
  Code.counter := -1;
  let expr =
    Ast.
      [
        Assign ("a", Bop (Add, Int 1, Bop (Mul, Int 2, Int 3)));
        If
          ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
            [
              While
                ( Bop (And, Bop (Eq, Var "a", Int 1), Bop (Lt, Var "a", Int 5)),
                  [ Assign ("a", Bop (Add, Var "a", Int 1)) ] );
            ],
            [ Return (Some (Int 60)) ] );
      ]
  in
  let result = expr |> Code.normalize |> CCVector.to_array in
  (check (module QuadArray))
    "same array" result
    Code.
      [|
        (Mul, Const 2, Const 3, Temp 0);
        (Add, Const 1, Temp 0, Temp 1);
        (Assign, Temp 1, Empty, Temp 2);
        (Eq, Temp 2, Const 1, Const 5);
        (Goto, Const 15, Empty, Empty);
        (Lt, Temp 2, Const 5, Const 7);
        (Goto, Const 15, Empty, Empty);
        (Eq, Temp 2, Const 1, Const 9);
        (Goto, Const 16, Empty, Empty);
        (Lt, Temp 2, Const 5, Const 11);
        (Goto, Const 16, Empty, Empty);
        (Add, Temp 2, Const 1, Temp 3);
        (Assign, Temp 3, Empty, Temp 2);
        (Goto, Const 7, Empty, Empty);
        (Goto, Const 16, Empty, Empty);
        (Return, Const 60, Empty, Empty);
        (Nop, Empty, Empty, Empty);
      |]

let test_figure_8_7 : unit -> unit =
 fun () ->
  let example =
    Code.
      [|
        (Assign, Const 1, Empty, Name 1);
        (Assign, Const 1, Empty, Name 2);
        (Mul, Const 10, Name 1, Temp 1);
        (Add, Temp 1, Name 2, Temp 2);
        (Mul, Const 8, Temp 2, Temp 3);
        (Sub, Temp 3, Const 88, Temp 4);
        (Assign, Const 0, Empty, Name 3);
        (Add, Name 2, Const 1, Name 2);
        (Le, Name 2, Const 10, Const 2);
        (Add, Name 1, Const 1, Name 1);
        (Le, Name 1, Const 10, Const 1);
        (Assign, Const 1, Empty, Name 1);
        (Sub, Name 1, Const 1, Temp 5);
        (Mul, Const 88, Temp 5, Temp 6);
        (Assign, Const 1, Empty, Name 3);
        (Add, Name 1, Const 1, Name 1);
        (Le, Name 1, Const 10, Const 12);
      |]
  in
  let result =
    example |> CCVector.of_array |> Cfg.blocks_of_code |> Cfg.M.bindings
    |> List.map snd
  in
  let open CCVector in
  let module S = Cfg.S in
  (check (module BlockList))
    "same output" result
    Code.
      [
        {
          code = of_array [| (Assign, Const 1, Empty, Name 1) |];
          pred = S.of_list [];
          succ = S.of_list [ 1 ];
        };
        {
          code = of_array [| (Assign, Const 1, Empty, Name 2) |];
          pred = S.of_list [ 0; 9 ];
          succ = S.of_list [ 2 ];
        };
        {
          code =
            of_array
              [|
                (Mul, Const 10, Name 1, Temp 1);
                (Add, Temp 1, Name 2, Temp 2);
                (Mul, Const 8, Temp 2, Temp 3);
                (Sub, Temp 3, Const 88, Temp 4);
                (Assign, Const 0, Empty, Name 3);
                (Add, Name 2, Const 1, Name 2);
                (Le, Name 2, Const 10, Const 2);
              |];
          pred = S.of_list [ 1; 2 ];
          succ = S.of_list [ 2; 9 ];
        };
        {
          code =
            of_array
              [|
                (Add, Name 1, Const 1, Name 1); (Le, Name 1, Const 10, Const 1);
              |];
          pred = S.of_list [ 2 ];
          succ = S.of_list [ 1; 11 ];
        };
        {
          code = of_array [| (Assign, Const 1, Empty, Name 1) |];
          pred = S.of_list [ 9 ];
          succ = S.of_list [ 12 ];
        };
        {
          code =
            of_array
              [|
                (Sub, Name 1, Const 1, Temp 5);
                (Mul, Const 88, Temp 5, Temp 6);
                (Assign, Const 1, Empty, Name 3);
                (Add, Name 1, Const 1, Name 1);
                (Le, Name 1, Const 10, Const 12);
              |];
          pred = S.of_list [ 11; 12 ];
          succ = S.of_list [ 12 ];
        };
      ]

let _ =
  run "Test three address codegen"
    [
      ("Tests proper output", [ test_case "example 1" `Quick test_example_1 ]);
      ( "Tests flow graph creation",
        [
          test_case "modified figure 8.7 in dragon book" `Quick test_figure_8_7;
        ] );
    ]
