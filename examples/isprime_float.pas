var printInteger : (int64): void;
var printChar : (char): void;

function is_prime(n : double) : int64;
begin
  if n <= 1.0 then
    is_prime := 0
  else
  begin
    var divisor : double = 2.0;
    var prime_flag : int64 = 1; // 1 means true, 0 means false

    while divisor * divisor <= n do
    begin
      // Simulated modulo operation using a while loop
      var temp : double = n;
      while temp >= divisor do
      begin
        temp := temp - divisor;
      end;

      // If remainder is 0, it is not a prime
      if temp = 0.0 then
        prime_flag := 0;

      divisor := divisor + 1.0;
    end;

    is_prime := prime_flag;
  end;
end

begin
  // Should print 0 (not prime)
  printInteger(is_prime(9.0));
  printChar('\n');
  // Should print 1 (prime)
  printInteger(is_prime(17.0));
  printChar('\n');
end