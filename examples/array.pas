var printInteger : (integer): void;

function sumnums() : integer;
begin
    array := [0; 5];
    array[0] := 1;
    array[1] := 2;
    array[2] := 3;
    array[3] := 4;
    array[4] := 5;
    sum := 0;
    i := 0;
    while i < 5 do
    begin
      sum := sum + array[i];
      i := i + 1;
    end;
    sumnums := sum;
end

begin
    result := sumnums();
    // Should print "Result: 34"
    printInteger(result);
end