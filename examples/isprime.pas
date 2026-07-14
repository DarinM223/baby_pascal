var printInteger : (integer): void;

function is_prime(n : integer) : integer;
begin
  if n <= 1 then
    is_prime := 0
  else
  begin
    divisor := 2;
    prime_flag := 1; // 1 means true, 0 means false

    while divisor * divisor <= n do
    begin
      // Simulated modulo operation using a while loop
      temp := n;
      while temp >= divisor do
      begin
        temp := temp - divisor;
      end;

      // If remainder is 0, it is not a prime
      if temp = 0 then
        prime_flag := 0;

      divisor := divisor + 1;
    end;

    is_prime := prime_flag;
  end;
end

begin
  // Should print 0 (not prime)
  printInteger(is_prime(9));
  // Should print 1 (prime)
  printInteger(is_prime(17));
end