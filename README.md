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
    1. [Props](WriteLean/ClassicalLogic/Props.lean)
    2. [Raw Proofs](WriteLean/ClassicalLogic/RawProofs.lean)