Baby Pascal
-----------

A compiler for a minimal dialect of Pascal. It is similar to [this project](https://github.com/DarinM223/baby-pascal), the main differences are:

* `mllex` and `menhir` for the lexer and parser instead of a hand-rolled lexer and recursive descent + Pratt parser
* Coopers algorithm for computing dominators instead of Lengauer-Tarjan
* Zipper control flow graphs instead of LLVM-style control flow graphs
* Instruction selection based off of pattern matching on lists of trees instead of doing tile cutting on DAGs
* SSA chordal register allocation instead of linear scan

### TODO:

- [x] Lexer
- [x] Parser
- [x] Elaboration
- [x] Lower to control flow graph
- [x] SSA construction
- [x] Dead code elimination
- [x] Constant propagation
- [ ] Global value numbering
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