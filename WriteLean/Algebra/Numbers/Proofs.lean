import Mathlib

/- ================= rfl ================ -/

-- Some facts are definitionally true, use `rfl` for that
example : 2 + 1 = 3 := by rfl     -- definition of add easily works
example : (2:ℝ) + 1 = 3 := by
  -- rfl     -- not so straight forward from cauchy addition
  sorry


/- ================= norm_num ================ -/

-- if target has only numbers, `norm_num` will compute a normalized form, which might prove
example : (1:ℝ) / (5 - 1) = ((5:ℝ) + 1)/(5^2 - 1) := by
  norm_num      -- norm_num brought out a normalized form which is equal in both sides

example : (2:ℝ) ^ (-3:ℝ) = (1:ℝ) / 8 := by
  norm_num      -- negative power is also not an issue

example (x: ℝ) (f: ℝ → ℝ) : f (x * (3 + 2)) = f ((x * 5) / (3 - 2)) := by
  norm_num      -- will normalize "around" parts it cannot work with

example (x : ℝ) : (4 + 1) * x = x * 5 := by
  norm_num      -- normalized numbers, but can't infer anything on variables
  sorry

example : (4:ℝ) ^ ((1: ℝ) / 6) = 2 ^ ((1:ℝ) / 3) := by
  norm_num      -- doesn't work with fraction power
  sorry

example (x : ℝ) : √ 25 = 5 := by
  norm_num      -- fails on square roots too, but will work "around" it
  sorry

-- works for `<, ≤, ≠` too
example : 1 < 100 := by norm_num

-- `at h` will allow to do the normalization on a hypothesis

example (x: ℝ) (h: (5 + 1) * x = 3) : 6 * x = 3 := by
  norm_num at h     -- can do the normalization at a hypothesis
  assumption

example (x: ℝ) (h: (5 + 1) * x + 1 = 3) : 6 * x = 2 := by
  norm_num at h     -- but no side change
  sorry


/- ================= norm_cast ================ -/

-- `norm_cast` tries to take care of redundant casting at goal
example (a b : ℕ) (h: a = b) : (a:ℝ) = (b:ℝ) := by
  norm_cast      -- turned goal to `a = b`

-- `at h` changes hypothesis
example (a b c: ℕ) (h: (a:ℝ) + b = c + 3) (h' : c + 3 = 4) : a + b = 4 := by
  norm_cast at h      -- turns `↑a + ↑b = ↑c + 3` to `a + b = c + 3`
  rw [←  h']
  assumption

example (a : ℕ) (b : ℤ) (h: (a:ℝ) = b) : a = b := by
  norm_cast at h      -- works with mixed levels of casting too
