/-=================== PROOFS USING PROP DEFINITIONS ===================== -/

-- NOTE following examples (p : Prop) doesn't mean p is true, it says p is a proposition, (hp : p) says hp is a proof of p (hence p is true)

-- Proving an implication is just providing the function matching the types needed
example (p : Prop) : p → p := (fun (hp : p) => hp)

-- Utilizing an implication means to apply on the matching argument type
example (p q : Prop) (h: p → q) (hp : p) : q := h hp

-- Proving and and is just utilizing And.intro
example (p q : Prop) (hp: p) (hq: q) : (p ∧ q) := And.intro hp hq

-- Utilzing and and means to use structure methos left and right
example (p q : Prop) (h: p ∧ q) : p := And.left h
example (p q : Prop) (h: p ∧ q) : q := And.right h

-- Proving Or is a bit tricky, the simplest case is proving from one part
example (p q : Prop) (hp : p) : p ∨ q := Or.inl hp
example (p q : Prop) (hq : q) : p ∨ q := Or.inr hq

-- utilizing Or is almost always finding a common resultant, so this works via pattern matching
example (p q r : Prop) (hpq: p ∨ q) (hpr : p → r) (hqr : q → r) : r :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

-- Proving Iff means using Iff.intro
example (p q : Prop) (hpq: p → q) (hqp: q → p) : (p ↔ q) := Iff.intro hpq hqp

-- utilzing Iff means use structure methods mp and mpr to get implications
example (p q : Prop) (h: p ↔ q) (hp: p) : q := (Iff.mp h) hp
example (p q : Prop) (h: p ↔ q) (hq: q) : p := (Iff.mpr h) hq



/- ==================== TRUTH and FALSE ========================== -/

-- p and ¬ p imply false (remember ¬ p just means p → False)
example (p : Prop) (hp: p) (hnp : ¬ p) : False := hnp hp

-- p implies false is just ¬ p
example (p : Prop) (hp : p → False) : ¬ p := hp

-- from False follows any propostion, this is basically an empty matching, but parsing won't allow that so we have to go low level and use recursor
-- lean has a named theorem to abstract this `False.elim` which figures out what to match
example (p : Prop) (h: False) : p := False.rec (fun (_: False) => p) h
example (p : Prop) (h: False) : p := False.elim h

-- True is self-evident, well via the constructor
example : True := True.intro

-- not false is basically saying false => false, so provide such a function
example : ¬ False := fun (h: False) => h

-- unfortunately law of excluded middle is not so easy to derive, so just use lean's proof
example (p : Prop) : p ∨ ¬ p := Classical.em p


/- ====================== SOME EXAMPLES ==================== -/

-- distribution of and over or is done by constructing the final or from intial or
example (p q r : Prop) (h: p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) :=
  match h.right with
  | Or.inl hq => Or.inl (And.intro h.left hq)
  | Or.inr hr => Or.inr (And.intro h.left hr)

-- not p or q means p implies q: this is done by creating a function from p to q utilzing the or
example (p q : Prop) (h: ¬ p ∨ q) : p → q :=
  fun (hp : p) =>
    match h with
    | Or.inl hnp => False.elim (hnp hp)
    | Or.inr hq => hq
