open Alcotest
open Baby_pascal.Cfg
open Baby_pascal.Code
open Baby_pascal.Ssa_graph

let code_of_array arr =
  arr |> Array.map (fun (op, a, b, r) -> { op; a; b; r }) |> CCVector.of_array

let phis_of_array arr =
  arr |> Array.map (fun (r, ins) -> { r; Block.ins }) |> CCVector.of_array

module Packed (Sym : Baby_pascal.Intf.Sym) = struct
  include Sym

  module Addr = struct
    type t = Addr.t

    let pp fmt = function
      | Addr.Name (n, i) -> Format.fprintf fmt "%s%d" (get_name n) i
      | addr -> Addr.pp fmt addr

    let equal = Addr.equal
  end

  module Edge = struct
    type t = edge

    let pp fmt = function
      | Phi phi ->
          let pp_sep fmt () = Format.pp_print_char fmt ',' in
          Format.fprintf fmt "%a <- phi(%a)" Addr.pp phi.r
            (Format.pp_print_list ~pp_sep Addr.pp)
            phi.ins
      | Quad quad ->
          Format.fprintf fmt "%a <- %a %a, %a" Addr.pp quad.r pp_op quad.op
            Addr.pp quad.a Addr.pp quad.b

    let equal = equal_edge
  end
end

let test_figure_1 () =
  let open Packed (Baby_pascal.Intf.Sym.Make (Baby_pascal.Intf.Fresh.Make ())) in
  let sum, a, i, t1, t2, t3, t4 =
    ( get_sym "sum",
      get_sym "a",
      get_sym "i",
      get_sym "t1",
      get_sym "t2",
      get_sym "t3",
      get_sym "t4" )
  in
  let ssa =
    Block.
      [
        ( exit,
          {
            phis = CCVector.of_array [||];
            code = CCVector.of_array [||];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [ 1 ];
            succ = S.of_list [];
          } );
        ( entry,
          {
            phis = CCVector.of_array [||];
            code = CCVector.of_array [||];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [];
            succ = S.of_list [ 0 ];
          } );
        ( 0,
          {
            phis = phis_of_array [||];
            code =
              code_of_array
                [|
                  (Assign, Const 0, Empty, Name (sum, 0));
                  (Assign, Const 1, Empty, Name (i, 0));
                |];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [ entry ];
            succ = S.of_list [ 1 ];
          } );
        ( 1,
          {
            phis =
              phis_of_array
                [|
                  (Name (sum, 1), [ Name (sum, 0); Name (sum, 2) ]);
                  (Name (i, 1), [ Name (i, 0); Name (i, 2) ]);
                |];
            code =
              code_of_array
                [|
                  (Sub, Name (i, 1), Const 1, Name (t1, 0));
                  (Mul, Name (t1, 0), Const 4, Name (t2, 0));
                  (Add, Name (t2, 0), Name (a, 0), Name (t3, 0));
                  (Load, Name (t3, 0), Empty, Name (t4, 0));
                  (Add, Name (sum, 1), Name (t4, 0), Name (sum, 2));
                  (Add, Name (i, 1), Const 1, Name (i, 2));
                  (Le, Name (i, 2), Const 100, Const 0);
                |];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [];
            succ = S.of_list [ 1; exit ];
          } );
      ]
    |> List.to_seq |> M.of_seq
  in
  let ssa_graph = use_def_chains ssa |> Hashtbl.to_seq |> List.of_seq in
  check
    (list (pair (module Addr) (module Edge)))
    "Check ssa graph" ssa_graph
    [
      ( Name (4, 2),
        Quad { op = Add; a = Name (4, 1); b = Const 1; r = Name (4, 2) } );
      ( Name (1, 0),
        Quad { op = Add; a = Name (2, 0); b = Name (5, 0); r = Name (1, 0) } );
      ( Name (6, 0),
        Quad { op = Assign; a = Const 0; b = Empty; r = Name (6, 0) } );
      ( Name (2, 0),
        Quad { op = Mul; a = Name (3, 0); b = Const 4; r = Name (2, 0) } );
      (Name (4, 1), Phi { r = Name (4, 1); ins = [ Name (4, 0); Name (4, 2) ] });
      ( Name (6, 2),
        Quad { op = Add; a = Name (6, 1); b = Name (0, 0); r = Name (6, 2) } );
      ( Name (4, 0),
        Quad { op = Assign; a = Const 1; b = Empty; r = Name (4, 0) } );
      ( Name (3, 0),
        Quad { op = Sub; a = Name (4, 1); b = Const 1; r = Name (3, 0) } );
      ( Name (0, 0),
        Quad { op = Load; a = Name (1, 0); b = Empty; r = Name (0, 0) } );
      (Name (6, 1), Phi { r = Name (6, 1); ins = [ Name (6, 0); Name (6, 2) ] });
    ]

let test_figure_5 () =
  let open Packed (Baby_pascal.Intf.Sym.Make (Baby_pascal.Intf.Fresh.Make ())) in
  let s, i, a, b, f =
    (get_sym "s", get_sym "i", get_sym "a", get_sym "b", get_sym "f")
  in
  let ssa =
    Block.
      [
        ( exit,
          {
            phis = CCVector.of_array [||];
            code = CCVector.of_array [||];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [ 1 ];
            succ = S.of_list [];
          } );
        ( entry,
          {
            phis = CCVector.of_array [||];
            code = CCVector.of_array [||];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [];
            succ = S.of_list [ 0 ];
          } );
        ( 0,
          {
            phis = phis_of_array [||];
            code = code_of_array [| (Assign, Const 0, Empty, Name (s, 1)) |];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [ entry ];
            succ = S.of_list [ 1 ];
          } );
        ( 1,
          {
            phis =
              phis_of_array [| (Name (s, 2), [ Name (s, 1); Name (s, 3) ]) |];
            code =
              code_of_array
                [|
                  (Mul, Name (a, 0), Name (b, 0), Temp 1);
                  (Neg, Name (s, 2), Empty, Temp 2);
                  (Add, Temp 2, Temp 1, Name (s, 3));
                  (Lt, Name (i, 0), Const 0, Const 1);
                |];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [];
            succ = S.of_list [ 1; 2 ];
          } );
        ( 2,
          {
            phis = CCVector.of_array [||];
            code = code_of_array [| (Assign, Name (s, 2), Empty, Name (f, 0)) |];
            pcopies = CCVector.of_array [||];
            pred = S.of_list [ 1 ];
            succ = S.of_list [ exit ];
          } );
      ]
    |> List.to_seq |> M.of_seq
  in
  let ssa_graph = def_use_chains ssa |> Hashtbl.to_seq |> List.of_seq in
  check string "Check ssa graph"
    ([%show: (Addr.t * Edge.t) list] ssa_graph)
    "[(s2, f0 <- Code.Assign s2, Code.Addr.Empty);\n\
    \  (s2, (Code.Addr.Temp 2) <- Code.Neg s2, Code.Addr.Empty);\n\
    \  (s3, s2 <- phi(s1,s3)); (b0, (Code.Addr.Temp 1) <- Code.Mul a0, b0);\n\
    \  (a0, (Code.Addr.Temp 1) <- Code.Mul a0, b0); (s1, s2 <- phi(s1,s3));\n\
    \  ((Code.Addr.Temp 2), s3 <- Code.Add (Code.Addr.Temp 2), (Code.Addr.Temp \
     1));\n\
    \  (i0, (Code.Addr.Const 1) <- Code.Lt i0, (Code.Addr.Const 0));\n\
    \  ((Code.Addr.Temp 1), s3 <- Code.Add (Code.Addr.Temp 2), (Code.Addr.Temp \
     1))\n\
    \  ]"

let _ =
  run "SSA graph tests"
    [
      ( "use-def SSA graph tests",
        [
          test_case "Test figure 1 in Operator Strength Reduction paper" `Quick
            test_figure_1;
        ] );
      ( "def-use SSA graph tests",
        [
          test_case
            "Test figure 5 in Code Instruction Selection based on SSA-graphs \
             paper"
            `Quick test_figure_5;
        ] );
    ]
