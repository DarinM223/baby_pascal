var printInteger : (int64): void;

function fibonacci(n : int64) : int64;
begin
    if n <= 1 then
        fibonacci := n
    else
        fibonacci := fibonacci(n - 1) + fibonacci(n - 2);
end

begin
    var result: int64 = fibonacci(9);
    // Should print "34"
    printInteger(result);
end