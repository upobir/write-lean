import Mathlib
/-=================== Proofs ================= -/


/-=================== rfl ================= -/

-- `rfl` tactic proves a goal when the goal is proven just by following definition
example (a : Nat) : Nat.succ (Nat.succ a) = a + 2 := by
  rfl       -- you can follow the addition definition to find a + 2 = Nat.succ (Nat.succ a)

-- note rfl will only follow definitions, won't use hypothsis.
example (a : Nat) (f: Nat → Nat) (h: ∀ x: Nat, f x = x + 1) :  f a = a + 1 := by
  --refl              won't work
  sorry

-- some statements may feel like definition, but that is not their definition in lean
example : {a : Nat  | a = 2} = { 2 } := by
  rfl       -- works as this is definition

example : {a : Nat | a + 2 = 4} = { 2 } := by
  -- rfl       not definition
  sorry

-- can follow through multiple definition as long as no "inference" needed
example :
  let f := fun (x: Nat) => x + 1;
  let g := fun (x: Nat) => x;
  f (g 3) = 4 := by
  rfl             -- follows through several definitions

/- ================ let and show ================ -/
-- `let` is to name a variable to hide complexity. note let is not same as have, let defines stuffs
-- `show` can be used just after that to establish the goal to be definitionally equal format
example (a b c d: ℝ) : 1 + (a + b + c + d) = a + b + c + d + 1 := by
  let x := a+b+c+d
  show 1 + x = x + 1
  exact add_comm 1 x    -- x and a + b + c + d are amse


/-=================== rw & nth_rw ================= -/

-- `rw` uses a equivalence relation to do rewrites. here we'll only focus on =, but it works for any equivalence relation
-- rw will use equality lhs = rhs (provided inside []) to replace all occurences of lhs in goal by rhs.
example (a b c d : Nat) (hab : a = b) (hbcd : b = c + d) : a = c + d := by
  rw [hab]        -- goal changes from a = c + d to b = c + d
  assumption

-- you can also find rhs and change them to lhs
example (a b c d : Nat) (hab : b = a) (hbcd : b = c + d) : a = c + d := by
  rw [← hab]        -- goal changes from a = c + d to b = c + d, note the `←`
  assumption

-- you can do several replacement in one line
example (a b c d : Nat) (hab: a = b) (hbc: b = c + 1) (hcd: c = 2*d) : a = 2*d + 1 := by
  rw [hab, hbc, hcd]
  -- note last rfl is auto applied, rw does that

-- you can do rewrites at a hypothesis to change that too
example (a b c : Nat) (hab: a = 2 * b) (hbc : b = c) : a = 2 * c := by
  rw [hbc] at hab     -- hab changes from a = 2*b to a = 2*c
  assumption

-- rw will replace all occurences
example (a b : Nat) (h: a = b) : a + a = b + b := by
  rw [h]         -- replaces two a

-- rw can use any prop that has equality as final result, lean will match the arguments to match first occurence
example (a b : Nat) : (a + b) + c = c + (a + b) := by
  rw [add_comm]     -- add_comm requires two input x, y for x + y = y + x, here first match is at (a+b) + c, so x, y are determined as (a+b) and c

-- you can force which inputs to use by writing them
example (a b : Nat) : (a + b) + c = (b + a) + c := by
  rw [add_comm a]       -- just writing a forces it, but you could've wrote add_comm a _ or add_comm a b

-- note the auto matching may fool you into thinking multiple are getting matched
example (a b c d: Nat) : (a + b) * (c + d) = (b + a) * (d + c) := by
  -- rw [add_comm]       this matches to add_comm a b, so only first sum is matched
  rw [add_comm a, add_comm c]

-- WARNING, `rw` can't work when the equality you are using has a single term on left side which is a metavariable. so turn it to explicit and use
example (f: ℕ → ℕ) (h:  {x: ℕ} → f x = x) : f 1 = 1 := by
  rw [h]
example (f: ℕ → ℕ) (h: {x : ℕ} → x = f x) : 1 = f 1 := by
  -- rw [h]   -- fails
  nth_rw 1 [@h 1]

-- rw will replace all, to rewrite only one occurence use `nth_rw`
example (a b c d: Nat) (h1: b = a) (h2: b + c = d) : b + c + b = d + a := by
  -- rw [h1]              changes all b to a, bad
  nth_rw 2 [h1]           -- change only 2nd occurence to get b + c + a = d + a
  rw [h2]

/-=================== unfold ================= -/

def myfunc (n: Nat) : Nat := 2 * n

-- `unfold` replaces all definitions of something, note this might seem like same as rw, and to some degree it is. But rw will match arguments, so only match one of the terms
example (a : Nat) : myfunc a + myfunc b = 2 * a + 2 * b := by
  unfold myfunc     -- unfold replaced both myfunc, rw would replace only one due to arguments
  rfl

-- can unfold at hypothesis
example (a: Nat) (h: myfunc a = 6) : 2 * a = 6 := by
  unfold myfunc at h      -- changing h to 2 * a = 6
  assumption
