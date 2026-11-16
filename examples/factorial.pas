var printInteger : (int64): void;

function factorial(n : int64) : int64;
begin
  // Edge cases
  factorial := 0;
  if n = 0 then
    factorial := 1;

  if n > 0 then
  begin
    accumulator := 1;
    while n > 1 do
    begin
      accumulator := accumulator * n;
      n := n - 1;
    end;
    factorial := accumulator;
  end;
end

begin
  // Should print "120"
  printInteger(factorial(5));
end