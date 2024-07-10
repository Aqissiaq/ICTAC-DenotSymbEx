# Compositional Symbolic Semantics
Coq mechanization of "Compositional Symbolic Semantics"

## Contents
The development follows the paper, split into files:

- [Traces](./Traces.v) covers section 3,
- [TraceDL](./TraceDL.v) covers section 4
- [Programs](./Programs.v) covers section 5 and 6, 
    - [Deterministic.v](./Deterministic.v) covers section 5.2 (the while-fragment of programs),
- [Operational](./Operational.v) covers section 7, and
- [ProgramDL](./ProgramDL.v) covers section 8.
    
### Auxilliary materials
- [Expr](./Expr.v) contains the syntax of expressions, and
- [Syntax](./Syntax.v) the syntax of our languages Trace, NonDet and While.
- [Maps](./Maps.v) contains definitions and useful lemmas about total maps used to reason about substitutions and valuations
- [Utils](./Utils.v) contains various lemmas about sets, relations and other useful constructions

## Build
The included Makefile (created for Coq 8.16.1) should allow just
```sh
make
```
The output includes the assumptions of key theorems:
- function extensionality for equality of states
- ensemble extensionality for extensional equality of sets
- eq_rect for dependent induction on the operational semantics
- excluded middle (`classic`) for non-constructive results (those that require the halting problem)

To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```
