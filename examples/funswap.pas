var printInteger : (integer): void;
var printChar : (char): void;

function bar(x : integer, y : integer) : integer;
begin
  bar := x + y;
end

function foo(x : integer, y : integer) : integer;
begin
  foo := bar(y, x);
end

function hello(x : integer, y : integer, z : integer) : integer;
begin
  a := world(y, z, x);
  b := world(z, x, x);
  c := world(z, z, y);
  hello := a + b + c;
end

function world(x : integer, y : integer, z : integer) : integer;
begin
  a := foo(x, z);
  b := foo(y, x);
  c := foo(z, x);
  world := a + b + c;
end

begin
    result := foo(3, 4);
    // Should print "7"
    printInteger(result);
    printChar('\n');
    result2 := hello(1, 2, 3);
    // Should print "39"
    printInteger(result2);
    printChar('\n');
end