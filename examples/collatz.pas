var printInteger : (integer): void;

function collatz_steps(n : integer) : integer;
begin
  steps := 0;
  while n > 1 do
  begin
    // Check if n is even using simulated modulo 2
    temp := n;
    while temp >= 2 do
    begin
      temp := temp - 2;
    end;

    if temp = 0 then
      n := n / 2
    else
      n := 3 * n + 1;

    steps := steps + 1;
  end;
  collatz_steps := steps;
end

begin
  // Sequence for 6: 6 -> 3 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1 (8 steps)
  // Should print "Result: 8"
  printInteger(collatz_steps(6));
end
