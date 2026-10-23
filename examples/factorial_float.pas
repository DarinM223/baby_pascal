var printDouble : (double): void;

function factorial(n : double) : double;
begin
  // Edge cases
  factorial := 0.0;
  if n = 0.0 then
    factorial := 1.0;

  if n > 0.0 then
  begin
    accumulator := 1.0;
    while n > 1.0 do
    begin
      accumulator := accumulator * n;
      n := n - 1.0;
    end;
    factorial := accumulator;
  end;
end

begin
  // Should print "Result: 120.0000"
  printDouble(factorial(5.0));
end