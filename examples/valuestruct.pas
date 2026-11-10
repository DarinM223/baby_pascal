var printInteger : (integer): void;
var printDouble : (double): void;
var printChar : (char): void;
var printString : (*char): void;

procedure printStruct1(struct1 : { a : integer, b : double });
begin
  printInteger (struct1.a);
  printDouble (struct1.b);
end

procedure printStruct2(struct2 : { a : integer, b : double, c : integer, d : double });
begin
  printInteger (struct2.a);
  printDouble (struct2.b);
  printInteger (struct2.c);
  printDouble (struct2.d);
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

begin
  // Struct is 16 bytes so should be passed into an integer and a double
  // calling convention register.
  var struct1 : { a : integer, b : double };
  printStruct1(struct1);
  // Should allocate a new struct on the stack, copy the old struct,
  // and pass a pointer to the new struct.
  var struct2 : { a : integer, b : double, c : integer, d : double };
  printStruct2(struct2);
  // Should pass all four into a single integer register.
  var struct3 : { a : char, b : char, c : char, d : char };
  printStruct3(struct3);
  // Passes arrays in struct by value, accounts for padding.
  var struct4 : { a : [7]char, b : double };
  printStruct4(struct4);
end