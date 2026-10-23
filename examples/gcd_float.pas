var printDouble : (double): void;

function gcd(a : double, b : double) : double;
begin
  while b > 0.0 do
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
  // Should print "Result: 6.0000"
  printDouble(gcd(54.0, 24.0));
end
