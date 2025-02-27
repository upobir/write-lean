import Mathlib

/- ================ Weak Induction =============== -/

-- weak induction is baked into the definition of natural numbers. since that is the inductive type definition so we can use `cases` (but will need a name in that case, so not used)
theorem manual_induction (n: ℕ) (f : ℕ → ℕ) (hz : f 0 = 1) (h: ∀ k: ℕ, f (k + 1) = 2 * f k) : f n = 2 ^ n := by
  cases n with
  | zero =>   -- prove f 0 = 2^0
    rw [hz]
    norm_num
  | succ m =>   -- prove f (m+1) = 2^(m+1)
    rw [h, manual_induction m f hz h] -- have to use self to get proof of f m = 2^m
    ring

-- instead we use `induction` which additionally provides inductive hypothesis for each recursive argument in the inductive type's constructor
example (n: ℕ) (f : ℕ → ℕ) (hz : f 0 = 1) (h: ∀ k: ℕ, f (k + 1) = 2 * f k) : f n = 2 ^ n := by
  induction n with
  | zero =>   -- proce f 0 = 2^0
    rw [hz]
    norm_num
  | succ m hm =>  -- prove f (m+1) = 2^(m+1), get inductive hypothesis f m = 2^m
    rw [h, hm]
    ring

-- `induction'` is kind of better where no naming needed, instead the required hypothesis are named at first
example (n: ℕ) (f : ℕ → ℕ) (hz : f 0 = 1) (h: ∀ k: ℕ, f (k + 1) = 2 * f k) : f n = 2 ^ n := by
  induction' n with m hm    -- m and inductive hypothesis hm named here
  . rw [hz] -- proce f 0 = 2^0
    norm_num
  . rw [h, hm]  -- prove f (m+1) = 2^(m+1)
    ring

/- ================ Strong Induction =============== -/

-- use `Nat.strong_induction_on` which takes in implicit predicate `P`, `n`, a proof of `∀ n: ℕ, (∀ m < n, P m) → P n` to produce the proof of `P n`
example (n : ℕ) (f : ℕ → ℕ) (h: ∀ k : ℕ, f k = f (k/2)) : f n = f 0 := by
  have hi (k: ℕ ): (∀ m < k, f m = f 0) → f k = f 0 := by sorry -- indutive step
  exact Nat.strong_induction_on n hi
