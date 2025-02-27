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
4. Number Theory
    1. Natural Number Technique
        1. [Proofs](WriteLean/NumberTheory/NatNumberTechnique/Proofs.lean)


## Tactics
1. `exact`
2. `assumption`
3. `have`
4. `apply`
5. `intro`
6. `constructor`
7. `left`, `right`
8. `cases`
9. `trivial`
10. `exfalso`
11. `contradiction`
12. `contrapose`
13. `by_contra`
14. `rfl`
15. `rw`, `nth_rw`
16. `unfold`
17. `use`
18. `exists`
19. `obtain`
20. `norm_num`
21. `norm_cast`
22. `simp`
23. `field_simp`
24. `calc`
25. `ring`, `ring_nf`
26. `field_simp`
27. `induction`
