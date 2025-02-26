/- ===================== EQUALITY =================== -/

-- Equality is most fundamental, lean defines it as a generic dependent inductive type for all types
#check Eq

namespace learning

-- to understand equality well, let's redefine it ourselves, but only for nat numbers
-- note the definition, although the type depens on two Nats, only one constructor is possible which uses one nat, this forces the fact that both dependent nats must be same

inductive Eq : Nat → Nat → Prop where
  | refl (a : Nat) : Eq a a

-- reflexitivity is just the usage of `refl`
example (a : Nat) : Eq a a := Eq.refl a

-- symmetricity is tricky, note that when matching, the refl constructor can only return Eq a a, so compiler knows from that b and a must be same, so just creating Eq a a becomes enough.
example (a b : Nat) (h: Eq a b) : Eq b a :=
  match h with
  | Eq.refl a => Eq.refl a

-- Transitivity is like symmetricity, matching on hbc forces b and c to become one, so proving hab is enough
example (a b c : Nat) (hab : Eq a b) (hbc: Eq b c) : Eq a c :=
  match hbc with
  | Eq.refl b => hab

-- substitution is defined in lean generically, but let's do for Predicates only. same as before match on h to force a,b to be same then use ha
example (a b : Nat) (P : Nat → Prop) (h: Eq a b) (ha: P a) : P b :=
  match h with
  | Eq.refl a => ha

end learning
