import Mathlib
/-=================== Proofs ================= -/

/- ================== Universal Quantifier ================= -/

-- use `intro` like normal implication as universal quantifier is also just a function
example : ∀ x: Nat, x = x := by
  intro x         -- introduces x : Nat
  exact Eq.refl x

-- works with multiple variable too
example : ∀ x y : Nat, x + y = y + x := by
  intro x y
  rw [add_comm]

-- nothing special about using universal quantifier, as it's a function just apply
example (h: ∀ x: Nat, x ≥ 0) : 5 ≥ 0 := by
  exact h 5

-- there is a way to create for all by `revert` which brings a local variable from context to target, effectively creating for all. not sure why do this, i g to match it exact to some hypothesis?
example (n m: ℕ) (h': n = m) (h: ∀ n:ℕ, n = m → n+2 = m+1+1) : n+2 = m+1+1 := by
  revert n    -- takes n  (and also n=m as it depends on n) to target
  assumption

/- ================== Existantial Quantifier ================= -/

-- try `use` to provide values for existantial quantifier, if predicate easy will be done, or predicate will be goal, if you want you can provide predicate in one line too
example : ∃ x : Nat, x = 5 := by
  use 5
example : ∃ x : Nat, x > 4 := by
  use 5
  norm_num
example : ∃ x : Nat, x > 4 := by
  use 5, (by norm_num: 5 > 4)

-- can work with multiple exists too
example : ∃ x y: Nat, x = y := by
  use 5, 5

-- `exists` can also work, it can also do simple stuff, you can't provide proof in one line
example : ∃ x : Nat, x > 4 := by
  exists 5
example : ∃ x : ℝ, x^2 - x = 2 := by
  exists 2
  norm_num

-- works with multiple exists too
example : ∃ x y: Nat, x = y := by
  exists 5, 5

-- to utilize exists, you can extract them, use `obtain` (which is like extract, except erases the hypothesis), or use `cases` to use the inductive definition

example (P Q : Nat → Prop) (h: ∀ x: Nat, P x → Q x) (hp: ∃ x: Nat, P x) : ∃ x: Nat, Q x := by
  have ⟨x, hpx⟩ := hp   -- extract x and hpx: P x
  use x, h x hpx       -- use x and proof of Q x

example (P Q : Nat → Prop) (h: ∀ x: Nat, P x → Q x) (hp: ∃ x: Nat, P x) : ∃ x: Nat, Q x := by
  obtain ⟨x, hpx⟩ := hp   -- extract x and hpx: P x, s before, but now hp is gone
  use x, h x hpx

example (P Q : Nat → Prop) (h: ∀ x: Nat, P x → Q x) (hp: ∃ x: Nat, P x) : ∃ x: Nat, Q x := by
  cases hp with
  | intro x hpx =>        -- intro case has x and hpx : P x
    use x, h x hpx


/- ================= Common ================ -/

-- de morgan's law for ∀ and ∃
#check not_forall         --  (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
#check not_exists         --  (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
