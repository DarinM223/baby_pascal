open Alcotest
open Baby_pascal
let test_example_1 () =
  let program =
    {|
var hello : int64;

// adds two numbers
function add(a : int64, b : int64) : int64;
begin
    add := a + b;
end

// prints an int64
procedure foo(a : int64);
begin
    print(a);
end

begin
    result := add(1, 2);
    if result > 2 then
       print(result);
    if result <= 2 then
       result := result + 1
    else
       result := result + 2;
    foo(result);
end
|}
  in
  let program = Parse.parse_string program in
  let expected =
    {
      Ast.globals =
        [ { id = "hello"; typ = Ast.TInteger64; value = Ast.External } ];
      decls =
        [
          Ast.Procedure
            ( "foo",
              [ ("a", Ast.TInteger64) ],
              Ast.Group [ Ast.Call ("print", [ Ast.Var "a" ]) ] );
          Ast.Function
            ( "add",
              [ ("a", Ast.TInteger64); ("b", Ast.TInteger64) ],
              Ast.TInteger64,
              Ast.Group
                [
                  Ast.Assign
                    (Var "add", Ast.Bop (Ast.Add, Ast.Var "a", Ast.Var "b"));
                ] );
        ];
      main =
        Ast.Group
          [
            Ast.Assign (Var "result", Ast.Call ("add", [ Ast.Int 1; Ast.Int 2 ]));
            Ast.If
              ( Ast.Bop (Ast.Gt, Ast.Var "result", Ast.Int 2),
                Ast.Call ("print", [ Ast.Var "result" ]),
                Ast.Group [] );
            Ast.If
              ( Ast.Bop (Ast.Le, Ast.Var "result", Ast.Int 2),
                Ast.Assign
                  (Var "result", Ast.Bop (Ast.Add, Ast.Var "result", Ast.Int 1)),
                Ast.Assign
                  (Var "result", Ast.Bop (Ast.Add, Ast.Var "result", Ast.Int 2))
              );
            Ast.Call ("foo", [ Ast.Var "result" ]);
          ];
    }
  in
  (check
     (option Ast.(testable (pp_program pp_stmt) (equal_program equal_stmt))))
    "Produces proper program" (Some expected) program

let _ =
  run "Parser"
    [
      ( "Tests parses properly",
        [ test_case "example program 1" `Quick test_example_1 ] );
    ]
