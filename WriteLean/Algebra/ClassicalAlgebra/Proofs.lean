import Mathlib

/- ================ Common =============== -/
-- `rw` and `rfl` are common techniques (see Equality)

example  {α : Type} [HAdd α α α] (a b c d : α) (h: a + b = c) : c + d = a + b + d := by -- α is Nat, Int, Rat, Real
  rw [← h]

example (a : ℕ) : a + 1 + 1 = a + 2 := by rfl  -- Nat add definition easily proves this

-- `calc` is the way to do chain of equality stuff, we write a = b = c = ... chain, justifying each pair as a isolated proof
example (a b c : ℝ) (h: c = a + b) : c^2 = a^2 + 2*a*b + b^2 := by
  calc
    c^2 = (a+b)^2 := by rw [h]
            -- justifying c^2 = (a+b)^2
    _ = (a+b)*(a+b) := by exact pow_two (a+b)
            -- justifying (a+b)^2 = (a+b)*(a+b)
    _ = a*(a+b) + b*(a+b) := by exact add_mul a b (a+b)
            -- justifying (a+b)*(a+b) = a*(a+b) + b*(a+b)
    _ = a^2 + a*b + (b*a + b^2) := by rw[mul_add, mul_add, ← pow_two, ← pow_two]
            -- justifying a*(a+b) + b*(a+b) = a^2 + a*b + (b*a + b^2)
    _ = a^2 + (a*b + b*a) + b^2 := by rw [← add_assoc, add_assoc (a^2)]
            -- justifying a^2 + a*b + (b*a + b^2) = a^2 + (a*b + b*a) + b^2
    _ = a^2 + (a*b + a*b) + b^2 := by rw [mul_comm]
            -- justifying a^2 + (a*b + b*a) + b^2 = a^2 + (a*b + a*b) + b^2
    _ = a^2 + 2*a*b + b^2 := by rw [← two_mul, mul_assoc]
            -- justifying a^2 + (a*b + a*b) + b^2 = a^2 + 2*a*b + b^2

-- Common mistake is thinking it's all real when it can be some lower type, note that two expressions below are completely different!
example (a: ℕ) : a / (a + 1) + 1 = (2*a + 1) / (a + 1) := by sorry
example (a: ℝ) : a / (a + 1) + 1 = (2*a + 1) / (a + 1) := by sorry




/- ================= Reals and Rationals ======================== -/

-- most algebraic manipulation related to +,-,* can be done by `ring` which will prove algebraic identity for commutative semiring. Note it will not use hypothesis

example (x y: ℚ) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

example (x: ℚ) : 4*x / 2 + 5*x^2 = 10*x^2 / 2 + 2*x := by ring

example (x: ℚ) : (x + 5 -x) / 5 = 1 := by ring  -- will handle number division similar to norm_num

example (x: ℚ) : (x + 5 -x) / (2 + x) = (5) / (x + 2)  := by ring -- will work on separate parts of division

example (x: ℚ) : (x + 5) / (5 + x) = 1 := by
  ring      -- but won't do anything with division of variables, note it just brought a normal form
  sorry

example (x a: ℚ) : a ^ (2 + 1) = a ^ (0 + 3) := by ring -- natural power is also handled

example (x a: ℚ) : a ^ (-2:ℤ) = a ^ ((-1:ℤ)-1) := by
  -- ring -- exponent with ℝ or ℤ won't be handled by ring
  sorry

example (x: ℕ) (a: ℚ) : a ^ (x + 5) = a ^ (5 + x) := by
  ring   -- exponent in variable is ok if ℕ

-- but real or rational or int variable in exponent won't work
example (a: ℝ) (x: ℤ) : a ^ (x + 5) = a ^ (5 + x) := by
  -- ring
  sorry
example (a x: ℝ) : a ^ (x + 5) = a ^ (5 + x) := by
  -- ring
  sorry

example (x : ℚ) (f: ℚ → ℝ) : f (x + 4) = f (2 + x/2 + x/2 + 2) := by
  -- ring   -- won't work across non-ring boundaries
  sorry

-- when there are non-ring stuff in the target or target is not equality, use `ring_nf` which will only normalize ring stuff to a normalized form

example (x : ℚ) (f: ℚ → ℝ) : f (x + 4) = f (2 + x/2 + x/2 + 2) := by ring_nf -- normalized and recognized both side same

example (a x y: ℝ) (h: x = y) : a ^ (x + 5) = a ^ (5 + y) := by
  ring_nf  -- normalized, but still x and y don't match
  rw [h]

example (x: ℚ) (h: x > 2) : 3*x + x^2 + x > (4 * x + 6) / 2 - 3 := by
  ring_nf     -- cancelled out everything but didn't change any sides
  sorry

-- to handle division use `field_simp` this will try to create a normalized format from a equation and if you have hypothesis of non-zero ness, take those denominator to other side. most times, `ring` is enough after it

example (a b : ℝ) (h: a ≠ 0) (h': b > 3) : a * b / a * 2 / b = 2 := by
  field_simp    -- basically cancelled both a and b (figured out b ≠ 0)

example (a b : ℝ) (h: a ≠ 0)  : a * b / a * 2 / b = 2 := by
  field_simp    -- cancelled a, but not b (as not guaranteed to be non-zero)
  sorry;

-- field_simp is a bit surprising as it'd multiply to other side but sometimes fail to prove simple ring facts, typically ring is enough now
example (a b : ℝ) (h: a ≠ 0) (h': b ≠ 0) : a * b / (b * a) = 1 := by
  field_simp -- converts to a * b = b * a
  ring

-- field_simp tries to figure out non-zero hypothesis, such as products but if it can't provide it with []
example (a b c : ℝ) (h: a ≠ 0) (h' : b ≠ 0) (h'': c^2 ≠ 0) : (a*b) * c / (a*b) / c = 1 := by
  field_simp [right_ne_zero_of_mul h''] -- provided the additional fact that c ≠ 0

-- can simplify at hypothesis
example (a b c d : ℝ) (h: b ≠ 0) (h': d ≠ 0) (h'': a / b = c / d) : a * d = b * c := by
  field_simp at h''
  rw [h'']
  ring


/- ================= Integers ======================== -/

-- ring and ring_nf will still work as before, except for division
example (a b : ℤ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring

example (a b : ℤ) : 10 / 2 * a = 5 * a := by ring -- division with just ints (no variable) doable kine of like norm_num

example (a b : ℤ) : (10 * a) / 2 = 5 * a := by
  -- ring    -- int division is not normal division, so ring can't help even when simple calculation
  sorry

example (a b : ℤ) : (b) / (3 + 5*a) = (b) / (5*a + 3) := by
  -- ring    -- ring doesn't work as it requires division properties to handle stuff, even when obviously equal
  sorry

-- to handle division you actually have to take care, in fact most things are not even true, advice is to wrie out each step and try apply?
example: ∃ x y z : ℤ, x/z + y/z ≠ (x+y)/z := by
  use 7, 8, 5,
  by norm_num     -- 7 / 5 + 8 / 5 = 1 + 1 ≠ 3 = 15 / 5


/- ================= Naturals ======================== -/

-- ring and ring_nf will still work as before, except for division and subtraction
example (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

example (a b : ℕ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by
  -- ring       -- can't prove
  sorry

example (a b : ℕ) : (5 - a - 3) = 2 - a := by
  -- ring       -- can't prove as nat subtraction is not same as normal subtraction
  sorry

-- nat subtraction is also weird
example: ∃ a b c: ℕ, a + (b - c) ≠ a + b - c := by
  use 2, 2, 3
  norm_num    -- as 2 + (2 - 3) = 2 + 0 = 2 ≠ 1 = 4 - 3 = 2 + 2 - 3

example (a : ℕ) : (5 - 3 - a) = 2 - a := by ring    -- this works tho, as ring will do norm_num stuff

-- same thing about division like ℤ
