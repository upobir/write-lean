import Mathlib

/- ================= square roots ================ -/

-- sqrt_sq and sq_sqrt are the source of proofs generally
#check Real.sqrt_sq
#check Real.sq_sqrt

-- here's an example
example : √ 25 = 5 := by
  calc
  √ 25 = √ (5^2) := by norm_num
  _ = 5 := by
    apply Real.sqrt_sq  -- noly requires proving 5 > 0 now
    norm_num

-- or use `simp` as sqrt thorems are part of it.
example : √ 25 = 5 := by
  calc
  √ 25 = √ (5^2) := by norm_num
  _ = 5 := by simp

-- norm_num works in place of (√ )^2 due to nature of √ definition
example : (√ 5)^2 = 5 := by norm_num

-- note negatives have sqrt defined to be zero, use simp with definition or unfold then norm_num
example : √(-25) = 0 := by
  unfold Real.sqrt
  norm_num

example : √(-25) = 0 := by
  simp [Real.sqrt]  -- as simp dones't have the sqrt definition registered

/- ============== zero product ================ -/
-- any integer power = 0 implies value = 0, works for ℕ, ℤ, ℚ, ℝ
#check pow_eq_zero    -- a^n = 0 → a = 0

-- ab = 0 implies a = 0 ∨ b = 0, is useful in quadratics and many cases with multiple term product = 0, works for ℕ, ℤ, ℝ, ℚ
#check mul_eq_zero      -- a*b = 0 ↔ a = 0 ∨ b = 0, typically we use `mul_eq_zero.mp`


/- ============== discriminent →  ================== -/

#check discrim    -- defined as discrim(a, b, c) = b^2-4*a*c

#check discrim_eq_sq_of_quadratic_eq_zero  -- discrim = 0  => (2ax + b)^2
#check exists_quadratic_eq_zero     -- discrim = s^2 implies roots of quadratic exists
#check quadratic_eq_zero_iff    -- discrim = s^2 then (-b-s)/2a
#check quadratic_ne_zero_of_discrim_ne_sq    -- discrim ≠ s^2 then no real soln


/- ============ vieta's formula ==================== -/
#check vieta_formula_quadratic      -- sum of root = -linear coeff, product of root = constant coeff
