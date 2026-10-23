var printDouble : (double): void;

function fibonacci(n : double) : double;
begin
    if n <= 1.0 then
        fibonacci := n
    else
        fibonacci := fibonacci(n - 1.0) + fibonacci(n - 2.0);
end

begin
    result := fibonacci(9.0);
    // Should print "Result: 34.0"
    printDouble(result);
end