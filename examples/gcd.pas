var printInteger : (integer): void;

function gcd(a : integer, b : integer) : integer;
begin
  while b > 0 do
  begin
    // Simulated modulo: a = a % b
    while a >= b do
    begin
      a := a - b;
    end;

    // Swap a and b
    temp := a;
    a := b;
    b := temp;
  end;
  gcd := a;
end

begin
  // The GCD of 54 and 24 is 6
  // Should print "Result: 6"
  printInteger(gcd(54, 24));
end
