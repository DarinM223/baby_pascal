var printInteger : (int64): void;

function collatz_steps(n : int64) : int64;
begin
  var steps : int64 = 0;
  while n > 1 do
  begin
    // Check if n is even using simulated modulo 2
    var temp : int64 = n;
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
  // Should print "8"
  printInteger(collatz_steps(6));
end
