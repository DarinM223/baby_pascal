open Alcotest
open Baby_pascal
let test_example_1 () =
  let program =
    {|
var hello : integer;

// adds two numbers
function add(a : integer, b : integer) : integer;
begin
    add := a + b;
end

// prints an integer
procedure foo(a : integer);
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
      Ast.globals = [ ("hello", Ast.TInteger) ];
      decls =
        [
          Ast.Procedure
            ( "foo",
              [ ("a", Ast.TInteger) ],
              Ast.Group [ Ast.Call ("print", [ Ast.Var "a" ]) ] );
          Ast.Function
            ( "add",
              [ ("a", Ast.TInteger); ("b", Ast.TInteger) ],
              Ast.TInteger,
              Ast.Group
                [
                  Ast.Assign ("add", Ast.Bop (Ast.Add, Ast.Var "a", Ast.Var "b"));
                ] );
        ];
      main =
        Ast.Group
          [
            Ast.Assign ("result", Ast.Call ("add", [ Ast.Int 1; Ast.Int 2 ]));
            Ast.If
              ( Ast.Bop (Ast.Gt, Ast.Var "result", Ast.Int 2),
                Ast.Call ("print", [ Ast.Var "result" ]),
                Ast.Group [] );
            Ast.If
              ( Ast.Bop (Ast.Le, Ast.Var "result", Ast.Int 2),
                Ast.Assign
                  ("result", Ast.Bop (Ast.Add, Ast.Var "result", Ast.Int 1)),
                Ast.Assign
                  ("result", Ast.Bop (Ast.Add, Ast.Var "result", Ast.Int 2)) );
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
