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

function multi() : integer;
begin
    matrix := [[0; 4]; 4];
    matrix[0][0] := 1;
    matrix[0][1] := 2;
    matrix[0][2] := 3;
    matrix[0][3] := 4;
    matrix[1][0] := 1;
    matrix[1][1] := 2;
    matrix[1][2] := 3;
    matrix[1][3] := 4;
    matrix[2][0] := 1;
    matrix[2][1] := 2;
    matrix[2][2] := 3;
    matrix[2][3] := 4;
    matrix[3][0] := 1;
    matrix[3][1] := 2;
    matrix[3][2] := 3;
    matrix[3][3] := 4;
    sum := 0;
    x := 0;
    while x < 4 do
    begin
        y := 0;
        while y < 4 do
        begin
            sum := sum + matrix[x][y];
            y := y + 1;
        end;
        x := x + 1;
    end;
    multi := sum;
end

begin
    result := sumnums();
    // Should print "Result: 15"
    printInteger(result);
end