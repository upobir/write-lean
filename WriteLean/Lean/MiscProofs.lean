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

/- ================== rename_i ============== -/
-- when props are unnamed (due to other tactica), you can rename them via `rename_i`
example (p q r: Prop) : p → r → q → q := by
  intros  -- this introduces 2 unnamed variables
  rename_i _ hq     -- renames last 2, first one (r) nothing, second one (q) hq
  exact hq

/- ============== generalize ================== -/
-- `generalize` allows changing constants to values and using them as hypothesis. this is easier sometimes.
example (f g: ℝ → ℝ) (h: ∀ n: ℝ, f n = g n) : f 3 = g 3 := by
  generalize hx: (3:ℝ) = x  -- had to force real type or nat type wasn't changing f 3, g 3
  exact h x

/- ================== repeat and <;> ============== -/
-- if a part of proof repeats several times (for some reason) can use repeat which will repeat section as long as can
example : 1 < 2 ∧ 2 < 3 := by
  constructor
  repeat        -- repeat norm_num (twice) to prove 1 < 2 and 2 < 3
    norm_num

-- not exactly repeat but `_ <;> _` applies first tactice whch possibly creates multiple goal, then second tactic is applied on each
example (p q : Prop) (h: p ∧ q) : q ∧ p := by
  have ⟨hp, hq⟩ := h
  constructor <;> assumption    -- two goals both solved by assumption
