var printInteger : (int64): void;
var printDouble : (double): void;
var printChar : (char): void;
var printString : (^char): void;

type
  TStruct1 = record
    a: int64;
    b: double;
  end;
  TStruct2 = record
    a : int64;
    b : double;
    c : int64;
    d : double;
  end;

procedure printStruct1(struct1 : TStruct1);
begin
  printInteger (struct1.a);
  printDouble (struct1.b);
end

procedure modifyStruct1(struct1 : TStruct1);
begin
  struct1.a := struct1.a + 1;
  struct1.b := struct1.b + 1.0;
  printStruct1(struct1);
end

function makeStruct1(initA: int64, initB: double): TStruct1;
begin
  var struct1 : TStruct1;
  struct1.a := initA;
  struct1.b := initB;
  makeStruct1 := struct1;
end

procedure printStruct2(struct2 : TStruct2);
begin
  printInteger (struct2.a);
  printDouble (struct2.b);
  printInteger (struct2.c);
  printDouble (struct2.d);
end

procedure modifyStruct2(struct2 : TStruct2);
begin
  struct2.a := struct2.a + 1;
  struct2.b := struct2.b + 1.0;
  struct2.c := struct2.c + 1;
  struct2.d := struct2.d + 1.0;
  printStruct2(struct2);
end

function makeStruct2(initA: int64, initB: double): TStruct2;
begin
  var struct2 : TStruct2;
  struct2.a := initA;
  struct2.b := initB;
  struct2.c := 5;
  struct2.d := 6.0;
  makeStruct2 := struct2;
end

procedure printStruct3(struct3 : record a : char; b : char; c : char; d : char; end);
begin
  printChar (struct3.a);
  printChar (struct3.b);
  printChar (struct3.c);
  printChar (struct3.d);
end

procedure printStruct4(struct4 : record a : array[0..7] of char; b : double; end);
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

procedure printStruct5(struct5 : record a : double; b : double; c : double; d : double; end);
begin
  printDouble (struct5.a);
  printDouble (struct5.b);
  printDouble (struct5.c);
  printDouble (struct5.d);
end

procedure printStruct6(struct6 : record a : double; b : double; c : double; d : double; e : double; end);
begin
  printDouble (struct6.a);
  printDouble (struct6.b);
  printDouble (struct6.c);
  printDouble (struct6.d);
  printDouble (struct6.e);
end

// Result should be: "23.00000012.00000045.00000067.00000034.00000056.000000abcdefghijk7.000000"
// Tests that modifyStruct* doesn't modify the underlying struct because its passed by value
// for both register and stack passing.
begin
  // Struct is 16 bytes so should be passed into an int64 and a double
  // calling convention register.
  var struct1 : TStruct1;
  struct1.a := 1;
  struct1.b := 2.0;
  printStruct1(makeStruct1(1, 2.0));
  modifyStruct1(struct1);
  printStruct1(struct1);
  // Should allocate a new struct on the stack, copy the old struct,
  // and pass a pointer to the new struct.
  var struct2 : record a: int64; b: double; c: int64; d: double; end;
  struct2.a := 3;
  struct2.b := 4.0;
  struct2.c := 5;
  struct2.d := 6.0;
  printStruct2(makeStruct2(3, 4.0));
  modifyStruct2(struct2);
  printStruct2(struct2);
  // Should pass all four into a single int64 register.
  var struct3 : record a : char; b : char; c : char; d : char; end;
  struct3.a := 'a';
  struct3.b := 'b';
  struct3.c := 'c';
  struct3.d := 'd';
  printStruct3(struct3);
  // Passes arrays in struct by value, accounts for padding.
  var struct4 : record a : array[0..7] of char; b : double; end;
  struct4.a[0] := 'e';
  struct4.a[1] := 'f';
  struct4.a[2] := 'g';
  struct4.a[3] := 'h';
  struct4.a[4] := 'i';
  struct4.a[5] := 'j';
  struct4.a[6] := 'k';
  struct4.b := 7.0;
  printStruct4(struct4);
  // On AARCH64 this is a HFA that gets passed into floating point registers
  // On X86-64 System V this will be passed into stack.
  var struct5 : record a : double; b : double; c : double; d : double; end;
  struct5.a := 0.0;
  struct5.b := 1.0;
  struct5.c := 2.0;
  struct5.d := 3.0;
  printStruct5(struct5);
  // On both X86-64 and AARCH64 this will be passed on stack
  var struct6 : record a : double; b : double; c : double; d : double; e : double; end;
  struct6.a := 0.0;
  struct6.b := 1.0;
  struct6.c := 2.0;
  struct6.d := 3.0;
  struct6.e := 4.0;
  printStruct6(struct6);
  printChar('\n');
end