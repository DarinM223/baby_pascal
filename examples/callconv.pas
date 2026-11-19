var printInteger : (int64): void;
var printDouble : (double): void;
var printChar : (char): void;

function hello(a: int64, b: int64, c: int64, d: int64, e: int64, f: int64, g: int64, h: int64) : int64;
begin
  hello := a + b + c + d + e + f + (h - g);
end

function doublehello(a: double, b: double, c: double, d: double, e: double, f: double, g: double, h: double) : double;
begin
  doublehello := a + b + c + d + e + f + (h - g);
end

function world(a: int64) : int64;
begin
  var sum : int64 = 0;
  while a > 0 do
  begin
    var v : ^int64;
    v := alloca int64 8;
    v^ := a;
    sum := sum + v^;
    a := a - 1;
  end;
  world := sum;
end

function blah() : int64;
begin
  var a : ^int64;
  var b : ^int64;
  a := alloca int64 8;
  b := alloca int64 8;
  a^ := 3;
  b^ := 4;
  var c : int64 = a^ + b^;
  blah := c;
end

begin
  // 1 + 2 + 3 + 4 + 5 + 6 + 1 (8 - 7 instead of 7 - 8)
  // Should print "22"
  printInteger(hello(1, 2, 3, 4, 5, 6, 7, 8));
  printChar('\n');
  // 1 + 2 + 3 + 4 + 5 + 6 + 1 (8 - 7 instead of 7 - 8)
  // Should print "22.000000"
  printDouble(doublehello(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0));
  printChar('\n');
  // Should print "36"
  printInteger(world(8));
  printChar('\n');
  // Should print "7"
  printInteger(blah());
  printChar('\n');
end