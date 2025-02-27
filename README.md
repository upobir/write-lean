# write-lean

## Create Project
In current working directory
```sh
elan run 4.15.0 lake init .
```

## Build binary
```sh
lake build
```
Not needed for proving. Binary at `.lake/build/bin/<project-name>`

## Table of Contents

1. Lean
    1. [Basics](WriteLean/Lean/Basics.lean)
    2. [Types](WriteLean/Lean/Types.lean)
2. Classical Logic
    1. Propositional Logic
        1. [Basics](WriteLean/ClassicalLogic/PropositionalLogic/Basics.lean)
        2. [Raw Proofs](WriteLean/ClassicalLogic/PropositionalLogic/RawProofs.lean)
        3. [Proofs](WriteLean/ClassicalLogic/PropositionalLogic/Proofs.lean)
    2. Equality
        1. [Basics](WriteLean/ClassicalLogic/Equality/Basics.lean)
        2. [Proofs](WriteLean/ClassicalLogic/Equality/Proofs.lean)
    3. Predicate Logic
        1. [Basics](WriteLean/ClassicalLogic/PredicateLogic/Basics.lean)
        2. [Raw Proofs](WriteLean/ClassicalLogic/PredicateLogic/RawProofs.lean)
        3. [Proofs](WriteLean/ClassicalLogic/PredicateLogic/Proofs.lean)
3. Algebra
    1. Numbers
        1. [Basics](WriteLean/Algebra/Numbers/Basics.lean)
        2. [Proofs](WriteLean/Algebra/Numbers/Proofs.lean)
    2. Classical Algebra
        1. [Proofs](WriteLean/Algebra/ClassicalAlgebra/Proofs.lean)