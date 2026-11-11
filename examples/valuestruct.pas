var printInteger : (integer): void;
var printDouble : (double): void;
var printChar : (char): void;
var printString : ( *char ): void;

procedure printStruct1(struct1 : { a : integer, b : double });
begin
  printInteger (struct1.a);
  printDouble (struct1.b);
end

procedure modifyStruct1(struct1 : { a : integer, b : double });
begin
  struct1.a := struct1.a + 1;
  struct1.b := struct1.b + 1.0;
  printStruct1(struct1);
end

procedure printStruct2(struct2 : { a : integer, b : double, c : integer, d : double });
begin
  printInteger (struct2.a);
  printDouble (struct2.b);
  printInteger (struct2.c);
  printDouble (struct2.d);
end

procedure modifyStruct2(struct2 : { a : integer, b : double, c : integer, d : double });
begin
  struct2.a := struct2.a + 1;
  struct2.b := struct2.b + 1.0;
  struct2.c := struct2.c + 1;
  struct2.d := struct2.d + 1.0;
  printStruct2(struct2);
end

procedure printStruct3(struct3 : { a : char, b : char, c : char, d : char });
begin
  printChar (struct3.a);
  printChar (struct3.b);
  printChar (struct3.c);
  printChar (struct3.d);
end

procedure printStruct4(struct4 : { a : [7]char, b : double });
begin
  printChar (struct4.a[0]);
  printChar (struct4.a[1]);
  printChar (struct4.a[2]);
  printChar (struct4.a[3]);
  printChar (struct4.a[4]);
  printChar (struct4.a[5]);
  printChar (struct4.a[6]);
  printDouble (struct4.b);
end

// Result should be: "23.00000012.00000045.00000067.00000034.00000056.000000abcdefghijk7.000000"
// Tests that modifyStruct* doesn't modify the underlying struct because its passed by value
// for both register and stack passing.
begin
  // Struct is 16 bytes so should be passed into an integer and a double
  // calling convention register.
  var struct1 : { a : integer, b : double };
  struct1.a := 1;
  struct1.b := 2.0;
  modifyStruct1(struct1);
  printStruct1(struct1);
  // Should allocate a new struct on the stack, copy the old struct,
  // and pass a pointer to the new struct.
  var struct2 : { a : integer, b : double, c : integer, d : double };
  struct2.a := 3;
  struct2.b := 4.0;
  struct2.c := 5;
  struct2.d := 6.0;
  modifyStruct2(struct2);
  printStruct2(struct2);
  // Should pass all four into a single integer register.
  var struct3 : { a : char, b : char, c : char, d : char };
  struct3.a := 'a';
  struct3.b := 'b';
  struct3.c := 'c';
  struct3.d := 'd';
  printStruct3(struct3);
  // Passes arrays in struct by value, accounts for padding.
  var struct4 : { a : [7]char, b : double };
  struct4.a[0] := 'e';
  struct4.a[1] := 'f';
  struct4.a[2] := 'g';
  struct4.a[3] := 'h';
  struct4.a[4] := 'i';
  struct4.a[5] := 'j';
  struct4.a[6] := 'k';
  struct4.b := 7.0;
  printStruct4(struct4);
  printChar('\n');
end