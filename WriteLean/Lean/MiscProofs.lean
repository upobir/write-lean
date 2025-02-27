import Mathlib

/- ================ dot ================ -/
-- dot notation is to indent a portion of proof, this is used when multiple goals exist to separate out goals section. if indentation broken errors
example (p q : Prop) (hp: p) (hq: q) : p ∧ q := by
  constructor
  . exact hp
  . exact hq

-- works without dot too
example (p q : Prop) (hp: p) (hq: q) : p ∧ q := by
  constructor
  exact hp
  exact hq

example (p q r : Prop) (hp : p) (hpq: p → q) (hqr : q → r) : r := by
  apply hqr
  . apply hpq     -- can introduce in the middle, useless
    assumption


/- ================== repeat ============== -/
-- if a part of proof repeats several times (for some reason) can use repeat which will repeat section as long as can
example : 1 < 2 ∧ 2 < 3 := by
  constructor
  repeat        -- repeat norm_num (twice) to prove 1 < 2 and 2 < 3
    norm_num
