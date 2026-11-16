var printInteger : (int64): void;
var printChar : (char): void;

function bar(x : int64, y : int64) : int64;
begin
  bar := x + y;
end

function foo(x : int64, y : int64) : int64;
begin
  foo := bar(y, x);
end

function hello(x : int64, y : int64, z : int64) : int64;
begin
  a := world(y, z, x);
  b := world(z, x, x);
  c := world(z, z, y);
  hello := a + b + c;
end

function world(x : int64, y : int64, z : int64) : int64;
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