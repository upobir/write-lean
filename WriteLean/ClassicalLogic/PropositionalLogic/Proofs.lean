import Mathlib

/- ================== PROOFS ================ -/

-- tactics is the defacto way to prove stuff, not the "raw" definitions



/- ================== IMPLICATION ================ -/

-- `exact` to provide a raw construction
example (p: Prop) : p → p := by
  exact fun (hp : p) => hp      -- could've skipped "by exact"

-- `assumption` when one of the hypothesis is already goal
example (p q r : Prop) (hp: p) (hq: q) (hr: r) : p := by
  assumption -- as hp: p already a hypothesis

-- `have` is for forward proving by establishing facts
example (p q r s: Prop) (hp: p) (hpq : p → q) (hqr: q → r) (hrs: r → s) : s := by
  have hq : q := hpq hp     -- named fact establishment
  have : r := hqr hq        -- unnamed, "this" name given by default
  have := hrs this          -- unamed, untyped, type is figured out, but good to write, also overwrites this
  exact this                -- the final this is the type, so use exact

-- `apply` is for reverse proving, you show goal is proved by an implication, so goal changes to the hypothesis of that implication
example (p q r s: Prop) (hp: p) (hpq: p → q) (hpqr : p → q → r) (hrs: r → s) : s := by
  apply hrs                 -- goal changes to r
  apply hpqr                -- goal matched to final target in p→q→r, so tow goals now p and q
  . assumption              -- goal p is proved by assumption directly
  . apply hpq               -- goal q is again changed to p by apply
    exact hp

-- `intro` allows assuming hypothesis to prove an implication
example (p q r: Prop) (hpq : p → q) (hqr: q → r) : p → r := by
  intro hp              -- introduces p as hypothesis
  exact hqr (hpq hp)    -- applying on hp to get r finally

example (p q: Prop) : p → q → p := by
  intro hp hq            -- introduces p, then q
  assumption



/- ================== AND ================ -/

-- for `and` hypothesis use left and right to extract info
example (p q : Prop) (hpq : p ∧ q) : p := by exact hpq.left
example (p q : Prop) (hpq : p ∧ q) : q := by exact hpq.right

-- `constructor` basically sets multiple goals for structure goals, perfect for and
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  . assumption
  . assumption

-- but short hand `⟨ , ⟩` is better sometimes (for any structure)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨ hp, hq ⟩

-- symmetry is very useful sometimes
example (p q : Prop) (hpq: p ∨ q) : (q ∨ p) := by exact hpq.symm
example (p q : Prop) (hpq: p ∨ q) : (q ∨ p) := by apply Or.symm; assumption


/- ================== OR ================ -/

-- `left` , `right` work for inductive types with 2 constructors and makes one fo them goal, perfect for or introduction
example (p q : Prop) (hp : p) : p ∨ q := by
  left
  assumption
example (p q : Prop) (hq : q) : p ∨ q := by
  right
  assumption

-- `cases` creates constructors for every constructor of inductive type, naming them just like the construtors, best for or
example (p q r : Prop) (hpq : p ∨ q) (hpr: p → r) (hqr : q → r) : r := by
  cases hpq with
  | inl hp => apply hpr; assumption
  | inr hq => apply hqr; assumption

-- symmetry is very useful sometimes
example (p q : Prop) (hpq: p ∧ q) : (q ∧ p) := by exact hpq.symm
example (p q : Prop) (hpq: p ∧ q) : (q ∧ p) := by apply And.symm; assumption



/- ================== IFF ================ -/

-- use `mp` and `mpr` to extract parts
example (p q : Prop) (h: p ↔ q) : p → q := by exact h.mp
example (p q : Prop) (h: p ↔ q) : q → p := by exact h.mpr

-- use `constructor` or `⟨ , ⟩` like and above
example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by
  constructor
  . assumption
  . assumption

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := by exact ⟨ hpq, hqp ⟩

-- the symmetrical form with `symm`
example (p q : Prop) (h: p ↔ q) : q ↔ p := by exact h.symm
example (p q : Prop) (h: p ↔ q) : q ↔ p := by apply Iff.symm; assumption

-- due to iff being a equivalence relation, `rw` can be used to replace equivalent props
example (p q r s : Prop) (hpq : p ↔ q) (h: (q ∧ r) → s) : (p ∧ r) → s := by
  rw [hpq]    -- change all p to q in goal
  assumption

example (p q r s : Prop) (hpq : p ↔ q) (h: (q ∧ r) → s) : (p ∧ r) → s := by
  rw [← hpq] at h    -- change all q to p in h, converting it to goal
  assumption



/- ================== TRUTH, FALSE, NOT ================ -/

-- `trivial` brings forth True by suing simple stuff
example : True := by trivial

-- `exfalso` basically makes any goal to proving false (basically applying False.elim)
example (p: Prop) (hf: False) : p := by
  exfalso
  assumption

-- no special tactic for ¬ p really, just prove `p → False` and vice versa
-- `contradiction` is good for when assumption has `p` and `¬ p` to prove any goal
example (p q : Prop) (hp: p) (hnp : ¬p): q := by contradiction

-- p ∨ ¬ p is brought out by classical em
example (p : Prop) : p ∨ ¬ p := by exact Classical.em p

-- `¬¬a ↔ a` is useful in rewrites
#check Classical.not_not



/- ================== COMMON STUFF ================ -/

-- one part of or can be removed due to not hypothesis
#check Or.resolve_left      -- (h : a ∨ b) (na : ¬a) : b
#check Or.resolve_right     -- (h : a ∨ b) (nb : ¬b) : a
#check Or.neg_resolve_left  -- (h : ¬a ∨ b) (na : a) : b
#check Or.neg_resolve_right -- (h : a ∨ ¬b) (nb : b) : a


-- de morgan's law, weird naming I know
#check not_and_or             -- ¬(a ∧ b) ↔ ¬a ∨ ¬b
#check not_or                 -- ¬(p ∨ q) ↔ ¬p ∧ ¬q


-- `contrapose` tactic changes goal
example (p q : Prop) (h: ¬ p → ¬ q) : (q → p) := by
  contrapose -- changes goal to ¬ p → ¬ q
  assumption
