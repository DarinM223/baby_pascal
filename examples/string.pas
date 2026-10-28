var printChar : (char): void;
var printString : (*char): void;

begin
    printString(&"hello\n");
    s1 := "world\n";
    printString(&s1);
    s2 := "xylophone";
    c1 := s1[0];
    c2 := s2[0];
    if c1 < c2 then begin
        printChar(c1);
        printString(&" is less than ");
        printChar(c2);
        printChar('\n');
    end
    else if c1 = c2 then begin
        printChar(c1);
        printString(&" is equal to ");
        printChar(c2);
        printChar('\n');
    end
    else begin
        printChar(c1);
        printString(&" is greater than ");
        printChar(c2);
        printChar('\n');
    end;
end