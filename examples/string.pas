var printChar : (char): void;
var printString : (^char): void;

begin
    printString(@"hello\n");
    var s1 : array[0..6] of char := "world\n";
    printString(@s1);
    var s2 : array[0..9] of char := "xylophone";
    var c1 : char := s1[0];
    var c2 : char := s2[0];
    if c1 < c2 then begin
        printChar(c1);
        printString(@" is less than ");
        printChar(c2);
        printChar('\n');
    end
    else if c1 = c2 then begin
        printChar(c1);
        printString(@" is equal to ");
        printChar(c2);
        printChar('\n');
    end
    else begin
        printChar(c1);
        printString(@" is greater than ");
        printChar(c2);
        printChar('\n');
    end;
end