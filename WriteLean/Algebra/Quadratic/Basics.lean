import Mathlib

/- =========== nonnegative reals ============== -/
-- to work with functions that require positive reals (such as squre root) nnreal or non-negative reals are defined
#check NNReal

variable (x : NNReal)
#check x.val          -- the underlying real value
#check x.property     -- proof of the property that 0 ≤ x


/- ============ square root ================= -/
-- squre root is defined to work on casted NNReal (turning to 0 if positive)
#check Real.sqrt
#check √(25)    -- 5
#check √(0)     -- 0
#check √(-25)   -- 0, as turns to 0 before doing NNReal.sqrt

example : √(-25) = 0 := by
  unfold Real.sqrt
  norm_num
