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
  var a : int64 := world(y, z, x);
  var b : int64 := world(z, x, x);
  var c : int64 := world(z, z, y);
  hello := a + b + c;
end

function world(x : int64, y : int64, z : int64) : int64;
begin
  var a : int64 := foo(x, z);
  var b : int64 := foo(y, x);
  var c : int64 := foo(z, x);
  world := a + b + c;
end

begin
    var result : int64 := foo(3, 4);
    // Should print "7"
    printInteger(result);
    printChar('\n');
    var result2 : int64 := hello(1, 2, 3);
    // Should print "39"
    printInteger(result2);
    printChar('\n');
end