/- ================== BASIC OF PROPS =================== -/

#check False -- Prop
#check True -- Prop

namespace learning
-- False is inductive with no constructor
inductive False : Prop

-- True does have constructor
inductive True : Prop where
  | intro : True

end learning


/- ======================= OPERATORS ==================== -/
section
variable (h1 h2 h3: Prop)

-- implication is more fundamental, it's just a function under the hood
#check h1 → h2

-- not, and, or, iff are defined as dependent types (click on names), and have defined operators
#check Not h1  -- a function that evals to h1 → False
#check ¬ h1

#check And h1 h2 -- a dependent structure with constructor And.intro h1 h2
#check h1 ∧ h2

#check Or h1 h2 -- a dependent inductive type with constructors inl and inr
#check h1 ∨ h2

#check Iff h1 h2 -- a dependent sturcture with constructor Iff.intro (h1 → h2) (h2 → h1)
#check h1 ↔ h2

end
