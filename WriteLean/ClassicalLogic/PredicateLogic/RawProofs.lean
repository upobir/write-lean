/-=================== PROOFS USING DEFINITIONS ===================== -/

/- ================== Universal Quantifier ================= -/

-- Proving universal quantifier means to create the corresponding function
example : ∀ x: Nat, x + 1 = Nat.succ x :=
  fun (x: Nat) => Eq.refl (x+1)   -- defininng the function

-- one will note how similar the proof is to following, this is because they are indeed same thing. a non-proof argument before : is same as that with forall quantifier.
example (x: Nat) : x + 1 = Nat.succ x := Eq.refl (x+1)

-- Utilizing the untiversal statment is to apply it on a value
example (h: ∀ x : Nat, x ≥ 0) : 5 ≥ 0 :=
  h 5  -- applying h on 5 produces a proof of 5 ≥ 0



/- ================== Existantial Quantifier ================= -/

-- Proving existantial qualifier means to use the constructor `intro`
example : ∃ x : Nat, x + 1 = 5 :=
  Exists.intro 4 (Eq.refl (4 + 1))   -- first argument is x, 2nd argument is proof of x + 1 = 5


-- Utilizing existantial qualifier means to use `match` on the expression, typicaly from one existantial you go to another
example (h: ∃ x: Nat, x = 5) : ∃ x: Nat, 5 = x :=
  match h with
  | Exists.intro x heq =>           -- for intro constructor there was x: Nat and heq : x = 5,
      Exists.intro x heq.symm       -- utilize x and heq.symm to prove existantial quantifier
