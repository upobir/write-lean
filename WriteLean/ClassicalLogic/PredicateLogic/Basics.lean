import Mathlib
/- ================== PREDICATE ================= -/

-- Predicates are any function that takes some arguments and in the end return a Proposition
def isZero (n: Nat) : Prop := (n = 0)    -- Nat → Prop
def isEqual (n m : Nat) : Prop := (n = m)   -- Nat → Nat → Prop

-- so note a predicate is not a proposition, but once you apply it, you get a proposition
#check isZero
#check isZero 1



/- ================== Universal Quantifier ================= -/

-- universal quantifier is a builtin feature of lean, suppose you have a type `α` and a predicate `P : α → Prop` then you can write `forall x: α, P x`
#check forall x: Nat, isZero x

-- this is synctactical sugar for `(x : α) → P x`
#check (x: Nat) → isZero x    -- same thing as `forall x : Nat, isZero x`

-- first point, `isZero x` has type `Prop` but it is not `Prop`, so the quantifier expression is not same as `(x: Nat) → Prop`.
-- something of type `(x: Nat) → Prop` maps a number (x) to a proposition
-- something of type `(x: Nat) → isZero x` maps a number (x) to a proof of `isZero x`

-- second point, `(x: Nat) →  isZero x` has type `Prop`, this is because in lean any function type where the last type is a Proposition, is also considered a proposition.
-- contrary, `(x: Nat) → Prop` is the type of a predicate, and this has type `Type 0`

-- you can write ∀ x y : Nat, x + y = y + x, following two are same
#check ∀ x y : Nat, x + y = y + x
#check ∀ x : Nat, ∀ y : Nat, x + y = y + x

-- there is synctactical sugar `∀ x: α, P α`
#check ∀ x : Nat, isZero x    -- same thing as `forall x: Nat, isZero x`

-- there are more synctactic sugar like `∀ x > 1, P x`, there are other inequalities and `x ∈ a`, `x ⊆ a` etc. note inquality cases only work assuming Nat type
#check ∀ x > 1, isZero x   -- this maps to `∀ x : ℕ, x > 1 → isZero x



/- ================== Existantial Quantifier ================= -/

-- exists is defined by `Exists` inductive class, that takes predicate (input type implict)
#check Exists

-- following 3 are same, so `exists` and `∃` are synctactical sugar
#check Exists isZero
#check exists n: Nat, isZero n
#check ∃ n: Nat, isZero n

-- as usual, `Exists isZero` is a proposition, but `Exists` itself needs a Predicate to form the proposition.

-- you can write ∃ x y : Nat, x + y = y + x, following two are same
#check ∃ x y : Nat, x + y = y + x
#check ∃ x : Nat, ∃ y : Nat, x + y = y + x

-- there are more synctactic sugar like `∃ x > 1, P x`, there are other inequalities and `x ∈ a`, `x ⊆ a` etc. note inquality cases only work assuming Nat type
#check ∃ x > 1, isZero x   -- this maps to `∃ x : ℕ, x > 1 ∧ isZero x
