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
    if struct2.a and struct2.c
    then
      sumfields := struct1.age + struct1.address.street + struct1.address.house_number + struct2.b
    else
      sumfields := struct1.age + struct1.address.street + struct1.address.house_number;
end

begin
    result := sumfields();
    // Should print "Result: 150"
    printInteger(result);
end