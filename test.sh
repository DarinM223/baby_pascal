dune exec compile -- -x86_64 examples/fibonacci.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "fibonacci compilation failed"
    exit 1
fi
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

dune exec compile -- -x86_64 examples/funswap.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "funswap compilation failed"
    exit 1
fi
./build.sh funswap.pas
./funswap.pas > funswap.pas.test
if cmp --silent funswap.pas.test examples/funswap.pas.expected; then
  echo "funswap test succeeded"
else
  echo "funswap test failed"
  echo "Diff:"
  diff funswap.pas.test examples/funswap.pas.expected
  exit 1
fi

dune exec compile -- -x86_64 examples/gcd.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "gcd compilation failed"
    exit 1
fi
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

dune exec compile -- -x86_64 examples/factorial.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "factorial compilation failed"
    exit 1
fi
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

dune exec compile -- -x86_64 examples/collatz.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "collatz compilation failed"
    exit 1
fi
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

dune exec compile -- -x86_64 examples/isprime.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "isprime compilation failed"
    exit 1
fi
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

dune exec compile -- -x86_64 examples/callconv.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "callconv compilation failed"
    exit 1
fi
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