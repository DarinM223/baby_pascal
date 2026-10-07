open Alcotest
open Baby_pascal
open Ast

let test_alignof_struct () =
  let struct1 = TRecord [ ("a", TBoolean); ("b", TInteger); ("c", TBoolean) ] in
  check int "Test struct 1" 8 (alignof struct1);
  check int "Test struct 2" 8
    (alignof (TRecord [ ("a", TBoolean); ("b", TInteger); ("c", struct1) ]))

let test_sizeof_struct () =
  (* "a" goes into offset 0
     "b" requires 8 byte alignment, adds 7 bytes of padding
     "c" goes into offset 16
     adds 7 bytes of padding for struct 8 byte alignment
     result should be 24 *)
  let struct1 = TRecord [ ("a", TBoolean); ("b", TInteger); ("c", TBoolean) ] in
  let result = sizeof struct1 in
  check int "Test struct 1" 24 result;
  (* "b" goes into offset 0
     "a" goes into offset 8
     "c" goes into offset 9
     adds 6 bytes of padding for struct 8 byte alignment
     result should be 16 *)
  let result =
    sizeof (TRecord [ ("b", TInteger); ("a", TBoolean); ("c", TBoolean) ])
  in
  check int "Test struct 2" 16 result;
  (* properly sizes nested structs *)
  let result =
    sizeof (TRecord [ ("a", TBoolean); ("b", TInteger); ("c", struct1) ])
  in
  check int "Test struct 3" 40 result

let _ =
  run "Test AST"
    [
      ("Tests alignof", [ test_case "structs" `Quick test_alignof_struct ]);
      ("Tests sizeof", [ test_case "structs" `Quick test_sizeof_struct ]);
    ]
