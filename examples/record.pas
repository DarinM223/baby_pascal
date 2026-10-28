var printInteger : (integer): void;

function sumfields() : integer;
begin
    var struct1 : { age : integer, address : { street : integer, house_number : integer } };
    struct1.age := 20;
    struct1.address.street := 50;
    struct1.address.house_number := 30;
    var struct2 : { a : boolean, b : integer, c : boolean };
    struct2.a := true;
    struct2.b := 50;
    struct2.c := true;
    var struct3 : { a : double, b : double, c : double };
    struct3.a := 1.0;
    struct3.b := 2.0;
    struct3.c := 3.0;
    if struct2.a and struct2.c and struct3.a + struct3.b + struct3.c = 6.0
    then
      sumfields := struct1.age + struct1.address.street + struct1.address.house_number + struct2.b
    else
      sumfields := struct1.age + struct1.address.street + struct1.address.house_number;
end

begin
    result := sumfields();
    // Should print "150"
    printInteger(result);
end