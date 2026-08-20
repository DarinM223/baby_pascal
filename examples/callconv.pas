var printInteger : (integer): void;

function hello(a: integer, b: integer, c: integer, d: integer, e: integer, f: integer, g: integer, h: integer) : integer;
begin
  hello := a + b + c + d + e + f + (h - g);
end

function world(a: integer) : integer;
begin
  sum := 0;
  while a > 0 do
  begin
    v := alloca integer 8;
    *v := a;
    sum := sum + *v;
    a := a - 1;
  end;
  world := sum;
end

begin
  // 1 + 2 + 3 + 4 + 5 + 6 + 1 (8 - 7 instead of 7 - 8)
  // Should print "Result: 22"
  printInteger(hello(1, 2, 3, 4, 5, 6, 7, 8));
  // Should print "Result: 36"
  printInteger(world(8));
end