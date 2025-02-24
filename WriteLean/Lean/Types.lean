/- Type hierarchy -/

#check Nat -- Type
#check Bool -- Type
#check String -- Type

#check Type -- Type 1
#check Type 0 -- Type 1
-- Type and Type 0 are same
#check Type 1 -- Type 2

-- Sort is more fundamental
#check Sort 0 -- Type or Type 0
#check Sort 1 -- Type 1
#check Sort 2 -- Type 2

#check Prop -- Type
-- Prop is like Nat, Bool, String

#check Prop → Prop -- Type
#check Nat → Type -- Type 1
#check Nat → Type → Type 1 -- Type 2
-- when expressions have types upto x, it's type is x+1


/- Type creations -/

-- Nat is defined by the 0 and succ
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

#eval MyNat.zero -- 0
#eval MyNat.succ MyNat.zero -- 1
#eval MyNat.succ (MyNat.succ MyNat.zero) -- 2

-- Bool is defined by the false and the true, mathematically this is same as prop, but Bool needed for programming
inductive MyBool : Type where
  | false : MyBool
  | true : MyBool

#eval MyBool.true
#eval MyBool.false

-- Prop has no construction, and in fact compiler removes all Props as they are a theoretical construct only
