var printInteger : (int64): void;
var printDouble : (double): void;
var printChar : (char): void;

function sumnums() : double;
begin
    var arr : array[0..5] of double := [0.0; 5];
    arr[0] := 1.0;
    arr[1] := 2.0;
    arr[2] := 3.0;
    arr[3] := 4.0;
    arr[4] := 5.0;
    var sum : double := 0.0;
    var i : int64 := 0;
    while i < 5 do
    begin
      sum := sum + arr[i];
      i := i + 1;
    end;
    sumnums := sum;
end

function multi() : int64;
begin
    var matrix : array[0..4, 0..4] of int64;
    matrix[0][0] := 1;
    matrix[0][1] := 2;
    matrix[0][2] := 3;
    matrix[0][3] := 4;
    matrix[1][0] := 5;
    matrix[1][1] := 6;
    matrix[1, 2] := 7;
    matrix[1][3] := 8;
    matrix[2][0] := 9;
    matrix[2][1] := 10;
    matrix[2][2] := 11;
    matrix[2, 3] := 12;
    matrix[3][0] := 13;
    matrix[3][1] := 14;
    matrix[3][2] := 15;
    matrix[3][3] := 16;
    var sum : int64 := 0;
    var x : int64 := 0;
    while x < 4 do
    begin
        var y : int64 := 0;
        while y < 4 do
        begin
            sum := sum + matrix[x,y];
            y := y + 1;
        end;
        x := x + 1;
    end;
    multi := sum;
end

begin
    var result : double := sumnums();
    // Should print "15.000000"
    printDouble(result);
    printChar('\n');
    var result2 : int64 := multi();
    // Should print "136"
    printInteger(result2);
    printChar('\n');

    var arr : array[5..10] of int64;
    // arr[4] and arr[10] should not compile, out of bounds
    arr[5] := 1;
    arr[6] := 2;
    arr[7] := 3;
    arr[8] := 4;
    arr[9] := 5;
    // runtime bounds checks aren't done yet, so these could go out of bounds
    var i : int64 := 5;
    while i < 10 do
    begin
        printInteger(arr[i]);
        printChar('\n');
        i := i + 1;
    end;
end