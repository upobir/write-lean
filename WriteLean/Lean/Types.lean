/- =================== TYPE HIERARCHY =================== -/

#check Nat -- Type
#check Bool -- Type
#check String -- Type

#check Type -- Type 1
#check Type 0 -- Type 1
-- Type and Type 0 are same
#check Type 1 -- Type 2

#check Prop -- Type
-- Prop is like Nat, Bool, String

#check Prop → Prop -- Type
#check Nat → Type -- Type 1
#check Nat → Type → Type 1 -- Type 2
-- when expressions have types upto x, it's type is x+1

-- so the chain of types/universes is `Prop : Type 0 : Type 1 : Type 2 ....`
-- we use inductive types to create inhabitants/types inside of these like
-- True False : Prop
-- Nat Bool : Type 0
-- These types have instances (but instances themselves are not types)
-- True.intro h : True
-- Nat.zero n : Nat


/- ==================== TYPE CREATION ======================== -/

namespace learning
-- Nat is defined by the 0 and succ
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

#eval Nat.zero -- 0
#eval Nat.succ Nat.zero -- 1
#eval Nat.succ (Nat.succ Nat.zero) -- 2

-- Bool is defined by the false and the true, mathematically this is same as prop, but Bool needed for programming
inductive Bool : Type where
  | false : Bool
  | true : Bool

#eval Bool.true
#eval Bool.false

-- Prop has no construction, and in fact compiler removes all Props as they are a theoretical construct only

end learning
