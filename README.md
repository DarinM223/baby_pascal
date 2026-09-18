Baby Pascal
-----------

A compiler for a minimal dialect of Pascal. It is similar to [this project](https://github.com/DarinM223/baby-pascal), the main differences are:

* `mllex` and `menhir` for the lexer and parser instead of a hand-rolled lexer and recursive descent + Pratt parser
* Coopers algorithm for computing dominators instead of Lengauer-Tarjan
* Zipper control flow graphs instead of LLVM-style control flow graphs
* Instruction selection based off of pattern matching on lists of trees instead of doing tile cutting on DAGs
* SSA chordal register allocation instead of linear scan

### Building

To build the compiler, first install opam and create an opam switch for OCaml 4.14 and then run:

```
opam install dune ocaml-lsp-server odoc ocamlformat utop
opam install . --deps-only
dune build
```

To compile a file like `examples/fibonacci.pas`, run:

```
dune exec compile -- -x86_64 examples/fibonacci.pas
```

for X86-64 with Linux calling conventions, or:

```
dune exec compile -- -aarch64 examples/fibonacci.pas
```

for AARCH64 with Linux calling conventions.

### Testing

Testing assumes that you are using a Linux machine with X86-64.
To test examples with X86-64, first make sure `gcc` and `as` are installed,
and then run the `./test.sh` script.

To test with AARCH64, first install:

```
sudo apt-get install gcc-arm-linux-gnueabihf libc6-dev-armhf-cross qemu-user-static libc6-dev-arm64-cross gcc-aarch64-linux-gnu gdb-multiarch
```

Then to run the test script with AARCH64 compilation:
```
AARCH=1 ./test.sh
```

### TODO:

- [x] Lexer
- [x] Parser
- [x] Elaboration
- [x] Lower to control flow graph
- [x] SSA construction
- [x] Dead code elimination
- [x] Constant propagation
- [x] Global value numbering
- [ ] Strength reduction
- [x] Critical edge splitting
- [ ] E-graph based optimizations
- [x] Undag into list of trees
- [x] X86 Instruction selection (basic)
- [ ] ARM Instruction selection
- [x] Loop nesting tree
- [x] Block execution frequency
- [x] SSA reconstruction
- [x] Spilling based off of next-use distances
- [x] Preference-based register allocation
- [x] Randomized testing for register shuffles in register allocation
- [x] Lower parallel moves
- [ ] Comprehensive IR fuzz testing
- [ ] Add floats to language
- [ ] Test spilling and register allocation with multiple register classes
- [ ] Add arrays to language
- [ ] Add structs to language
- [ ] Autovectorization