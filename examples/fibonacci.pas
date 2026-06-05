var printInteger : (integer): void;

function fibonacci(n : integer) : integer;
begin
    if n <= 1 then
        fibonacci := n
    else
        fibonacci := fibonacci(n - 1) + fibonacci(n - 2);
end

begin
    result := fibonacci(9);
    // Should print "Result: 34"
    printInteger(result);
end