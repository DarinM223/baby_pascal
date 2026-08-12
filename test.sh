dune exec compile examples/fibonacci.pas &> /dev/null
./build.sh fibonacci.pas
./fibonacci.pas > fibonacci.pas.test
if cmp --silent fibonacci.pas.test examples/fibonacci.pas.expected; then
  echo "fibonacci test succeeded"
else
  echo "fibonacci test failed"
  echo "Diff:"
  diff fibonacci.pas.test examples/fibonacci.pas.expected
  exit 1
fi

# dune exec compile examples/funswap.pas &> /dev/null
# ./build.sh funswap.pas
# ./funswap.pas > funswap.pas.test
# if cmp --silent funswap.pas.test examples/funswap.pas.expected; then
#   echo "funswap test succeeded"
# else
#   echo "funswap test failed"
#   echo "Diff:"
#   diff funswap.pas.test examples/funswap.pas.expected
#   exit 1
# fi

dune exec compile examples/gcd.pas &> /dev/null
./build.sh gcd.pas
./gcd.pas > gcd.pas.test
if cmp --silent gcd.pas.test examples/gcd.pas.expected; then
  echo "gcd test succeeded"
else
  echo "gcd test failed"
  echo "Diff:"
  diff gcd.pas.test examples/gcd.pas.expected
  exit 1
fi

dune exec compile examples/factorial.pas &> /dev/null
./build.sh factorial.pas
./factorial.pas > factorial.pas.test
if cmp --silent factorial.pas.test examples/factorial.pas.expected; then
  echo "factorial test succeeded"
else
  echo "factorial test failed"
  echo "Diff:"
  diff factorial.pas.test examples/factorial.pas.expected
  exit 1
fi

dune exec compile examples/collatz.pas &> /dev/null
./build.sh collatz.pas
./collatz.pas > collatz.pas.test
if cmp --silent collatz.pas.test examples/collatz.pas.expected; then
  echo "collatz test succeeded"
else
  echo "collatz test failed"
  echo "Diff:"
  diff collatz.pas.test examples/collatz.pas.expected
  exit 1
fi

dune exec compile examples/isprime.pas &> /dev/null
./build.sh isprime.pas
./isprime.pas > isprime.pas.test
if cmp --silent isprime.pas.test examples/isprime.pas.expected; then
  echo "isprime test succeeded"
else
  echo "isprime test failed"
  echo "Diff:"
  diff isprime.pas.test examples/isprime.pas.expected
  exit 1
fi

dune exec compile examples/callconv.pas &> /dev/null
./build.sh callconv.pas
./callconv.pas > callconv.pas.test
if cmp --silent callconv.pas.test examples/callconv.pas.expected; then
  echo "callconv test succeeded"
else
  echo "callconv test failed"
  echo "Diff:"
  diff callconv.pas.test examples/callconv.pas.expected
  exit 1
fi