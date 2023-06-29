# ICTAC: Denotational Semantics for Symbolic Execution
Coq mechanization of "Denotational Semantics for Symbolic Execution" for ICTAC23 submission.

## Contents
### Main results
    - [BigStep](./BigStep.v) covers section 2-3, culminating in Theorem 1: `concrete_symbolic_correspondence`
    - [SmallStep](./SmallStep.v) defines and describes the small-step trace semantics of section 4, and
    - [Correspondence](./Correspondence.v) proves Theorem 2: `big_small_correspondence`
    - [Direct](./Direct.v) proves Proposition 1 (`trace_if_direct` and `direct_if_trace`) and its corollaries `correctness` and `completeness`.
    
### Auxilliary materials
    - [Expr](./Expr.v) contains the syntax of expressions, and
    - [Syntax](./Syntax.v) the syntax of our toy language WHILE
    - [Maps](./Maps.v) contains definitions and useful lemmas about total maps used to reason about substitutions and valuations
    - [Limits](./Limits.v) contains the use of constructive description to handle non-termination
    - Finally, [BigStepExamples](./BigStepExamples.v) contains some examples runs of the big step semantics

## Build
The included Makefile (created for Coq 8.16.1) should allow just
```sh
make
```

To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```
