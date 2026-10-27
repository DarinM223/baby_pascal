var printString : (*char): void;

begin
    printString(&"hello");
    s := "world";
    printString(&s);
end