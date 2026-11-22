open Alcotest
open Baby_pascal

let typ = testable Ast.pp_typ Ast.equal_typ
let typed_expr = testable Ast.Typed.pp_expr Ast.Typed.equal_expr

let widen_integer_types_assignment =
  Ast.
    [
      (TInteger64, TInteger64, Some TInteger64);
      (TInteger64, TInteger32, Some TInteger64);
      (TInteger16, TInteger64, Some TInteger64);
      (TInteger64, TChar, None);
      (TDouble, TSingle, None);
      (TBoolean, TInteger32, None);
      (TArray (TInteger64, 1, 5), TArray (TInteger64, 1, 5), None);
      (TArray (TInteger32, 0, 6), TArray (TInteger16, 0, 6), None);
      (TArray (TInteger16, 0, 6), TArray (TInteger64, 0, 6), None);
      (TRecord [], TRecord [], None);
      (TArray (TInteger16, 0, 10), TPointer TInteger16, None);
      (TPointer TInteger16, TArray (TInteger16, 0, 10), None);
    ]

let widen_integer_assignment_tests =
  let go (ty1, ty2, expected) =
    let test_name =
      Format.asprintf "Integer widening assignment test for types %a and %a"
        Ast.pp_typ ty1 Ast.pp_typ ty2
    in
    test_case test_name `Quick @@ fun () ->
    check (option typ) test_name expected
      (Check.widen_integer_types ~initialization:false (ty1, ty2))
  in
  List.map go widen_integer_types_assignment

let widen_integer_types_initialization =
  Ast.
    [
      (TInteger64, TInteger64, Some TInteger64);
      (TInteger64, TInteger32, Some TInteger64);
      (TInteger16, TInteger64, Some TInteger64);
      (TInteger64, TChar, None);
      (TDouble, TSingle, None);
      (TBoolean, TInteger32, None);
      ( TArray (TInteger64, 1, 5),
        TArray (TInteger64, 1, 5),
        Some (TArray (TInteger64, 1, 5)) );
      (TArray (TInteger64, 1, 5), TArray (TInteger64, 0, 5), None);
      (TArray (TInteger64, 1, 5), TArray (TInteger64, 1, 6), None);
      ( TArray (TInteger32, 0, 6),
        TArray (TInteger16, 0, 6),
        Some (TArray (TInteger32, 0, 6)) );
      ( TArray (TInteger16, 0, 6),
        TArray (TInteger64, 0, 6),
        Some (TArray (TInteger64, 0, 6)) );
      (TRecord [], TRecord [], Some (TRecord []));
      ( TRecord [ ("a", TInteger64) ],
        TRecord [ ("a", TInteger16) ],
        Some (TRecord [ ("a", TInteger64) ]) );
      (TRecord [ ("a", TInteger64) ], TRecord [ ("b", TInteger64) ], None);
      ( TRecord [ ("a", TInteger64); ("b", TInteger32); ("c", TInteger16) ],
        TRecord [ ("a", TInteger16); ("b", TInteger64); ("c", TInteger32) ],
        Some
          (TRecord [ ("a", TInteger64); ("b", TInteger64); ("c", TInteger32) ])
      );
      ( TRecord [ ("a", TInteger64); ("b", TInteger32); ("c", TInteger16) ],
        TRecord [ ("a", TInteger16); ("b", TChar); ("c", TInteger32) ],
        None );
      ( TRecord [ ("a", TInteger64); ("b", TInteger32); ("c", TInteger16) ],
        TRecord [ ("a", TInteger64); ("c", TInteger16); ("b", TInteger32) ],
        None );
      ( TRecord [ ("a", TInteger64); ("b", TInteger32); ("c", TInteger16) ],
        TRecord [ ("a", TInteger64); ("b", TInteger32) ],
        None );
      (TArray (TInteger16, 0, 10), TPointer TInteger16, None);
      (TPointer TInteger16, TArray (TInteger16, 0, 10), None);
      ( TRecord
          [ ("a", TArray (TRecord [ ("a", TArray (TInteger16, 0, 5)) ], 0, 5)) ],
        TRecord
          [ ("a", TArray (TRecord [ ("a", TArray (TInteger64, 0, 5)) ], 0, 5)) ],
        Some
          (TRecord
             [
               ("a", TArray (TRecord [ ("a", TArray (TInteger64, 0, 5)) ], 0, 5));
             ]) );
    ]

let widen_integer_initialization_tests =
  let go (ty1, ty2, expected) =
    let test_name =
      Format.asprintf "Integer widening initialization test for types %a and %a"
        Ast.pp_typ ty1 Ast.pp_typ ty2
    in
    test_case test_name `Quick @@ fun () ->
    check (option typ) test_name expected
      (Check.widen_integer_types ~initialization:true (ty1, ty2))
  in
  List.map go widen_integer_types_initialization

let widen_float_types_assignment =
  Ast.
    [
      (TDouble, TDouble, Some TDouble);
      (TDouble, TSingle, Some TDouble);
      (TSingle, TDouble, Some TDouble);
      (TDouble, TInteger64, None);
      (TBoolean, TSingle, None);
      (TArray (TDouble, 1, 5), TArray (TDouble, 1, 5), None);
      (TArray (TSingle, 0, 6), TArray (TSingle, 0, 6), None);
      (TArray (TSingle, 0, 6), TArray (TDouble, 0, 6), None);
      (TRecord [], TRecord [], None);
      (TArray (TSingle, 0, 10), TPointer TSingle, None);
      (TPointer TSingle, TArray (TSingle, 0, 10), None);
    ]

let widen_float_assignment_tests =
  let go (ty1, ty2, expected) =
    let test_name =
      Format.asprintf "Float widening assignment test for types %a and %a"
        Ast.pp_typ ty1 Ast.pp_typ ty2
    in
    test_case test_name `Quick @@ fun () ->
    check (option typ) test_name expected
      (Check.widen_float_types ~initialization:false (ty1, ty2))
  in
  List.map go widen_float_types_assignment

let widen_float_types_initialization =
  Ast.
    [
      (TDouble, TDouble, Some TDouble);
      (TDouble, TSingle, Some TDouble);
      (TSingle, TDouble, Some TDouble);
      (TDouble, TChar, None);
      (TBoolean, TSingle, None);
      ( TArray (TDouble, 1, 5),
        TArray (TDouble, 1, 5),
        Some (TArray (TDouble, 1, 5)) );
      (TArray (TDouble, 1, 5), TArray (TDouble, 0, 5), None);
      (TArray (TDouble, 1, 5), TArray (TDouble, 1, 6), None);
      ( TArray (TSingle, 0, 6),
        TArray (TSingle, 0, 6),
        Some (TArray (TSingle, 0, 6)) );
      ( TArray (TSingle, 0, 6),
        TArray (TDouble, 0, 6),
        Some (TArray (TDouble, 0, 6)) );
      (TRecord [], TRecord [], Some (TRecord []));
      ( TRecord [ ("a", TDouble) ],
        TRecord [ ("a", TSingle) ],
        Some (TRecord [ ("a", TDouble) ]) );
      (TRecord [ ("a", TDouble) ], TRecord [ ("b", TDouble) ], None);
      ( TRecord [ ("a", TDouble); ("b", TSingle); ("c", TSingle) ],
        TRecord [ ("a", TSingle); ("b", TDouble); ("c", TSingle) ],
        Some (TRecord [ ("a", TDouble); ("b", TDouble); ("c", TSingle) ]) );
      ( TRecord [ ("a", TDouble); ("b", TSingle); ("c", TSingle) ],
        TRecord [ ("a", TSingle); ("b", TChar); ("c", TSingle) ],
        None );
      ( TRecord [ ("a", TDouble); ("b", TSingle); ("c", TSingle) ],
        TRecord [ ("a", TDouble); ("c", TSingle); ("b", TSingle) ],
        None );
      ( TRecord [ ("a", TDouble); ("b", TSingle); ("c", TSingle) ],
        TRecord [ ("a", TDouble); ("b", TSingle) ],
        None );
      (TArray (TSingle, 0, 10), TPointer TSingle, None);
      (TPointer TSingle, TArray (TSingle, 0, 10), None);
      ( TRecord
          [ ("a", TArray (TRecord [ ("a", TArray (TSingle, 0, 5)) ], 0, 5)) ],
        TRecord
          [ ("a", TArray (TRecord [ ("a", TArray (TDouble, 0, 5)) ], 0, 5)) ],
        Some
          (TRecord
             [ ("a", TArray (TRecord [ ("a", TArray (TDouble, 0, 5)) ], 0, 5)) ])
      );
    ]

let widen_float_initialization_tests =
  let go (ty1, ty2, expected) =
    let test_name =
      Format.asprintf "Float widening initialization test for types %a and %a"
        Ast.pp_typ ty1 Ast.pp_typ ty2
    in
    test_case test_name `Quick @@ fun () ->
    check (option typ) test_name expected
      (Check.widen_float_types ~initialization:true (ty1, ty2))
  in
  List.map go widen_float_types_initialization

let widen_expressions =
  let open Ast in
  let open Ast.Typed in
  [
    (TInteger64, (TInteger16, Int 1), (TInteger64, Int 1));
    (* widened_typ is expected to be a valid widened type
       obtained through widen_integer_types or widen_float_types *)
    (TChar, (TInteger16, Int 1), (TChar, Int 1));
    ( TPointer TInteger64,
      (TPointer TInteger16, Addrof (TInteger16, Int 1)),
      (TPointer TInteger64, Addrof (TInteger64, Int 1)) );
    ( TArray (TArray (TArray (TInteger64, 0, 5), 0, 6), 0, 7),
      ( TArray (TArray (TArray (TInteger16, 0, 5), 0, 6), 0, 7),
        Array
          ( ( TArray (TArray (TInteger16, 0, 5), 0, 6),
              Array
                ((TArray (TInteger16, 0, 5), Array ((TInteger16, Int 0), 5)), 6)
            ),
            7 ) ),
      ( TArray (TArray (TArray (TInteger64, 0, 5), 0, 6), 0, 7),
        Array
          ( ( TArray (TArray (TInteger64, 0, 5), 0, 6),
              Array
                ((TArray (TInteger64, 0, 5), Array ((TInteger64, Int 0), 5)), 6)
            ),
            7 ) ) );
  ]

let widen_expressions_tests =
  let go (ty, expr, expected) =
    let test_name =
      Format.asprintf "Expression widening test type %a expression %a"
        Ast.pp_typ ty Ast.Typed.pp_expr expr
    in
    test_case test_name `Quick @@ fun () ->
    check typed_expr test_name expected (Check.widen_expression ty expr)
  in
  List.map go widen_expressions

let _ =
  run "Test Check"
    [
      ( "Test widening integer types",
        widen_integer_assignment_tests @ widen_integer_initialization_tests );
      ( "Test widening float types",
        widen_float_assignment_tests @ widen_float_initialization_tests );
      ("Test widening expressions to type", widen_expressions_tests);
    ]
