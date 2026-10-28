var printDouble : (double): void;

function collatz_steps(n : double) : double;
begin
  steps := 0.0;
  while n > 1.0 do
  begin
    // Check if n is even using simulated modulo 2
    temp := n;
    while temp >= 2.0 do
    begin
      temp := temp - 2.0;
    end;

    if temp = 0.0 then
      n := n / 2.0
    else
      n := 3.0 * n + 1.0;

    steps := steps + 1.0;
  end;
  collatz_steps := steps;
end

begin
  // Sequence for 6: 6 -> 3 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1 (8 steps)
  // Should print "8.000000"
  printDouble(collatz_steps(6.0));
end
