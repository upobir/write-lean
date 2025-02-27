import Mathlib

/- ============= Plugging in ============= -/
-- plugging in is just `rw` see equality and classsical algebra
example (a b : ℝ) (h₁ : a = b + 3) (h₂: a + b = 9) : b = 3 := by
  rw [h₁] at h₂     -- plug in value of a in 2nd expression
  sorry


/- ============== linear manipulation ============= -/
-- We generally take linear combination of equations to find some other target expression. this is the main job of `linarith`, it takes into account the hypothesis and their linear combinations
example (a b : ℝ) (h₁ : a + b = 9) (h₂ : b - a = 3) : b = 6 := by
  linarith      -- automatically figure out h₁/2 + h₂/2 gives result

-- can work if there are complex parts (just abstracts them)
example (a :ℝ) (f: ℝ → ℝ) (h: f a + a * 2 = 2) (h' : f a = 7) : a = -5/2 := by
  linarith      -- treatd f(a) as just a term

-- won't work inside the complexities of course
example (a :ℝ) : a + 1 = 1 + a := by linarith
example (a :ℝ) (f: ℝ → ℝ) : f (a + 1) = f (1 + a) := by
  -- linarith     -- won't go inside terms that are abstracted
  sorry

-- linarith works with ℚ too. for ℤ there are limitations, interactions of divsion with variables is beyond linarith's capabilities so they are also considered abstrations
example (a b : ℝ) (h: 1 + a/2 = b) (h' : 3*b = 9) : (a + 2*b)/2 = 5 := by
  linarith -- reals ok
example (a b : ℝ) (h: 1 + a/2 = b) (h' : 3*b = 9) : a/2 + b = 5 := by
  linarith -- ok here as no division relation with variables needed to be messed with
example (a b : ℤ) (h: 1 + a/2 = b) (h' : 3*b = 9) : (a + 2*b)/2 = 5 := by
  -- linarith   -- will need to break the a/2, so can't help
  sorry

-- for ℕ, additionally no subtraction relation will be broken
example (a b : ℤ) (h₁ : a + b = 10) (h₂: a - b = 2) : a = 6 := by linarith   -- int ok
example (a b : ℕ) (h₁ : a + b = 10) (h₂: b + 2 = 6) : a = 6 := by linarith   -- no subtractions needed to break
example (a b : ℕ) (h₁ : a + b = 10) (h₂: a - b = 2) : a = 6 := by
  -- linarith   -- a combination will need to break the (a-b), so not ok
  sorry

-- for the problems with ℕ, ℤ, there is `omega`, linarith for ints, these basically tries to work with linarith but also splits to cases when facing divsion, subtraction etc.
example (a b : ℤ) (h: 1 + a/2 = b) (h' : 3*b = 9) : (a + 2*b)/2 = 5 := by omega
example (a b : ℕ) (h₁ : a + b = 10) (h₂: a - b = 2) : a = 6 := by omega
