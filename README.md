# Fully Symbolic Semantics
Coq mechanization of "Fully Symbolic Semantics"

## Contents
The development follows the paper (except for DL, for now), with one file per section.
### Main results
- [Traces](./Traces) covers section 3.
- [Programs](./Programs.v) covers section 5 and 6, and
- [Operational](./Operational.v) covers section 7
    
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

To update the Makefile use
```sh
coq_makefile -f _CoqProject -o Makefile
```
