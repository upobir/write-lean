import Mathlib
import Lean

/- ============= Natural ============== -/

-- There's Natural Numbes already, known as `Nat`, but Mathlib provides alias. Defined as an inductive class following peano axioms
#check Nat
#check ℕ

-- There are usual operators
#eval 10 + 8
#eval 10 - 8    -- WARNING, see below
#eval 5 * 8
#eval 16 / 8    -- WARNING, see below
#eval 10 ^ 2
#eval 16 % 5    -- WARNING, see below

-- to not allow any errors, a - b is 0 whern a < b, a / b is floor division, a / 0 = 0, a % 0 = a
#eval 8 - 10
#eval 1 / 2
#eval 5 / 0
#eval 5 % 0

/- ============= Integer ============== -/

-- Integers defined also as Inductive class with unique mapping for negatives
#check Int
#check ℤ

-- operators as before
#eval 10 + -8
#eval -10 - 8
#eval 5 * -8
#eval 16 / -8    -- WARNING, see below
#eval -10 ^ 2
#eval 16 % -5    -- WARNING, see below

-- to not allow any errors, a / b is floor division, a / 0 = 0, a % 0 = a
#eval -5 / 4
#eval -5 / 0
#eval -5 % 0

-- also note that a negative number was used above to force integer, instead we can do a cast
#eval 8 - 10        -- 0, ℕ
#eval (8:ℤ) - 10    -- -2, ℤ

/- ============= Rationals ============== -/

-- Rationals defined also as Inductive class but it's a bit different, with
#check Rat
#check ℚ

-- Note you may think decimals will make rational, but NO, those are IEEE floats for programming, there is no explicit way to create rationals, use casting
#check 8.5
#check (17:ℚ) / 2

-- operators as before, but modulo is useless (tho defined)
#eval (11:ℚ) + 3 / 4
#eval (10:ℚ) - 101 / 2
#eval (5:ℚ) * 2 / 3
#eval (16:ℚ) / 3       -- WARNING, see below
#eval ((1:ℚ)/2) ^ 3    -- only nat exponent
#eval (5:ℚ) % 4        -- useless

-- For division, a / 0 = 0
#eval (5:ℚ) / 0


/- ============= Reals ============== -/

-- Reals are defined via cauchy sequence
#check Real
#check ℝ

-- operators, but some are not evaluatable due to nature of cauchy, there is also square root
#eval (1:ℝ) + 1
#eval (3:ℝ) - 4
#eval (-1:ℝ) * 1
#check (4:ℝ) / 2    -- eval won't evaluate the cauchy, but defined
#check (5:ℝ) ^ ((1:ℝ)/2) -- eval won't evaluate the cauchy, but deifned
#check (5:ℝ) % 3  -- probably useless
#check √ 5        -- wont' compute, but exists
