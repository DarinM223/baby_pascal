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

if [ -v AARCH ]; then
  dune exec compile -- -arm examples/fibonacci.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "fibonacci compilation failed"
      exit 1
  fi
  ./build-aarch.sh fibonacci.pas
  ./run-aarch.sh fibonacci.pas > fibonacci.pas.test
  if cmp --silent fibonacci.pas.test examples/fibonacci.pas.expected; then
    echo "fibonacci test succeeded"
  else
    echo "fibonacci test failed"
    echo "Diff:"
    diff fibonacci.pas.test examples/fibonacci.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/funswap.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "funswap compilation failed"
      exit 1
  fi
  ./build-aarch.sh funswap.pas
  ./run-aarch.sh funswap.pas > funswap.pas.test
  if cmp --silent funswap.pas.test examples/funswap.pas.expected; then
    echo "funswap test succeeded"
  else
    echo "funswap test failed"
    echo "Diff:"
    diff funswap.pas.test examples/funswap.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -arm64 examples/gcd.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "gcd compilation failed"
      exit 1
  fi
  ./build-aarch.sh gcd.pas
  ./run-aarch.sh gcd.pas > gcd.pas.test
  if cmp --silent gcd.pas.test examples/gcd.pas.expected; then
    echo "gcd test succeeded"
  else
    echo "gcd test failed"
    echo "Diff:"
    diff gcd.pas.test examples/gcd.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -arm examples/factorial.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "factorial compilation failed"
      exit 1
  fi
  ./build-aarch.sh factorial.pas
  ./run-aarch.sh factorial.pas > factorial.pas.test
  if cmp --silent factorial.pas.test examples/factorial.pas.expected; then
    echo "factorial test succeeded"
  else
    echo "factorial test failed"
    echo "Diff:"
    diff factorial.pas.test examples/factorial.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/collatz.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "collatz compilation failed"
      exit 1
  fi
  ./build-aarch.sh collatz.pas
  ./run-aarch.sh collatz.pas > collatz.pas.test
  if cmp --silent collatz.pas.test examples/collatz.pas.expected; then
    echo "collatz test succeeded"
  else
    echo "collatz test failed"
    echo "Diff:"
    diff collatz.pas.test examples/collatz.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/isprime.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "isprime compilation failed"
      exit 1
  fi
  ./build-aarch.sh isprime.pas
  ./run-aarch.sh isprime.pas > isprime.pas.test
  if cmp --silent isprime.pas.test examples/isprime.pas.expected; then
    echo "isprime test succeeded"
  else
    echo "isprime test failed"
    echo "Diff:"
    diff isprime.pas.test examples/isprime.pas.expected
    exit 1
  fi
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

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/callconv.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "callconv compilation failed"
      exit 1
  fi
  ./build-aarch.sh callconv.pas
  ./run-aarch.sh callconv.pas > callconv.pas.test
  if cmp --silent callconv.pas.test examples/callconv.pas.expected; then
    echo "callconv test succeeded"
  else
    echo "callconv test failed"
    echo "Diff:"
    diff callconv.pas.test examples/callconv.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/array.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "array compilation failed"
    exit 1
fi
./build.sh array.pas
./array.pas > array.pas.test
if cmp --silent array.pas.test examples/array.pas.expected; then
  echo "array test succeeded"
else
  echo "array test failed"
  echo "Diff:"
  diff array.pas.test examples/array.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/array.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "array compilation failed"
      exit 1
  fi
  ./build-aarch.sh array.pas
  ./run-aarch.sh array.pas > array.pas.test
  if cmp --silent array.pas.test examples/array.pas.expected; then
    echo "array test succeeded"
  else
    echo "array test failed"
    echo "Diff:"
    diff array.pas.test examples/array.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/record.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "record compilation failed"
    exit 1
fi
./build.sh record.pas
./record.pas > record.pas.test
if cmp --silent record.pas.test examples/record.pas.expected; then
  echo "record test succeeded"
else
  echo "record test failed"
  echo "Diff:"
  diff record.pas.test examples/record.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/record.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "record compilation failed"
      exit 1
  fi
  ./build-aarch.sh record.pas
  ./run-aarch.sh record.pas > record.pas.test
  if cmp --silent record.pas.test examples/record.pas.expected; then
    echo "record test succeeded"
  else
    echo "record test failed"
    echo "Diff:"
    diff record.pas.test examples/record.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/fibonacci_float.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "fibonacci_float compilation failed"
    exit 1
fi
./build.sh fibonacci_float.pas
./fibonacci_float.pas > fibonacci_float.pas.test
if cmp --silent fibonacci_float.pas.test examples/fibonacci_float.pas.expected; then
  echo "fibonacci_float test succeeded"
else
  echo "fibonacci_float test failed"
  echo "Diff:"
  diff fibonacci_float.pas.test examples/fibonacci_float.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/fibonacci_float.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "fibonacci_float compilation failed"
      exit 1
  fi
  ./build-aarch.sh fibonacci_float.pas
  ./run-aarch.sh fibonacci_float.pas > fibonacci_float.pas.test
  if cmp --silent fibonacci_float.pas.test examples/fibonacci_float.pas.expected; then
    echo "fibonacci_float test succeeded"
  else
    echo "fibonacci_float test failed"
    echo "Diff:"
    diff fibonacci_float.pas.test examples/fibonacci_float.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/gcd_float.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "gcd_float compilation failed"
    exit 1
fi
./build.sh gcd_float.pas
./gcd_float.pas > gcd_float.pas.test
if cmp --silent gcd_float.pas.test examples/gcd_float.pas.expected; then
  echo "gcd_float test succeeded"
else
  echo "gcd_float test failed"
  echo "Diff:"
  diff gcd_float.pas.test examples/gcd_float.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -arm64 examples/gcd_float.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "gcd_float compilation failed"
      exit 1
  fi
  ./build-aarch.sh gcd_float.pas
  ./run-aarch.sh gcd_float.pas > gcd_float.pas.test
  if cmp --silent gcd_float.pas.test examples/gcd_float.pas.expected; then
    echo "gcd_float test succeeded"
  else
    echo "gcd_float test failed"
    echo "Diff:"
    diff gcd_float.pas.test examples/gcd_float.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/factorial_float.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "factorial_float compilation failed"
    exit 1
fi
./build.sh factorial_float.pas
./factorial_float.pas > factorial_float.pas.test
if cmp --silent factorial_float.pas.test examples/factorial_float.pas.expected; then
  echo "factorial_float test succeeded"
else
  echo "factorial_float test failed"
  echo "Diff:"
  diff factorial_float.pas.test examples/factorial_float.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -arm examples/factorial_float.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "factorial_float compilation failed"
      exit 1
  fi
  ./build-aarch.sh factorial_float.pas
  ./run-aarch.sh factorial_float.pas > factorial_float.pas.test
  if cmp --silent factorial_float.pas.test examples/factorial_float.pas.expected; then
    echo "factorial_float test succeeded"
  else
    echo "factorial_float test failed"
    echo "Diff:"
    diff factorial_float.pas.test examples/factorial_float.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/collatz_float.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "collatz_float compilation failed"
    exit 1
fi
./build.sh collatz_float.pas
./collatz_float.pas > collatz_float.pas.test
if cmp --silent collatz_float.pas.test examples/collatz_float.pas.expected; then
  echo "collatz_float test succeeded"
else
  echo "collatz_float test failed"
  echo "Diff:"
  diff collatz_float.pas.test examples/collatz_float.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/collatz_float.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "collatz_float compilation failed"
      exit 1
  fi
  ./build-aarch.sh collatz_float.pas
  ./run-aarch.sh collatz_float.pas > collatz_float.pas.test
  if cmp --silent collatz_float.pas.test examples/collatz_float.pas.expected; then
    echo "collatz_float test succeeded"
  else
    echo "collatz_float test failed"
    echo "Diff:"
    diff collatz_float.pas.test examples/collatz_float.pas.expected
    exit 1
  fi
fi

dune exec compile -- -x86_64 examples/isprime_float.pas &> /dev/null
if [ $? -ne 0 ]; then
    echo "isprime_float compilation failed"
    exit 1
fi
./build.sh isprime_float.pas
./isprime_float.pas > isprime_float.pas.test
if cmp --silent isprime_float.pas.test examples/isprime_float.pas.expected; then
  echo "isprime_float test succeeded"
else
  echo "isprime_float test failed"
  echo "Diff:"
  diff isprime_float.pas.test examples/isprime_float.pas.expected
  exit 1
fi

if [ -v AARCH ]; then
  dune exec compile -- -aarch64 examples/isprime_float.pas &> /dev/null
  if [ $? -ne 0 ]; then
      echo "isprime_float compilation failed"
      exit 1
  fi
  ./build-aarch.sh isprime_float.pas
  ./run-aarch.sh isprime_float.pas > isprime_float.pas.test
  if cmp --silent isprime_float.pas.test examples/isprime_float.pas.expected; then
    echo "isprime_float test succeeded"
  else
    echo "isprime_float test failed"
    echo "Diff:"
    diff isprime_float.pas.test examples/isprime_float.pas.expected
    exit 1
  fi
fi