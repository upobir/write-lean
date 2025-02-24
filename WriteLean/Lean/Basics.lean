/- eval and check -/

-- check types

#check 1 -- Nat
#check true -- Bool
#check "abc" -- String

#check Nat -- Type
#check Bool -- Type
#check String -- Type

-- check final values

#eval 1 + 2 -- 3
#eval 1 - 2 -- -1
#eval 2 * 3 -- 6
#eval 4 / 3 -- 1 (floor division)
#eval 4 % 3 -- 1
#eval 2 ^ 3 -- 8

#eval "a" ++ "b" -- "ab"

#eval true && false -- false
#eval true || false -- true
#eval !true -- false




/- variable and function declare -/

def x := 1 -- type inferred
def y : Nat := 1 -- type set

def f1 (x: Nat) (y: Nat) : Nat := x + y -- normal
def f2 (x: Nat) (y: Nat) := x + y -- let return type be determined
def f3 : Nat → Nat → Nat := fun x => fun y => x + y -- anonymous function, note the type of f3
def f4 := fun (x: Nat) => fun (y: Nat) => x + y -- anonymous function, but type not given, so arguments need'em
def f5 : Nat → Nat → Nat := λ x => λ y => x + y -- lambda notation, note type of f5
def f6 := λ (x: Nat) => λ y => x + y -- lambda notation, but type not give, type of one argument is enough in this case

#check f1 -- function (Nat → Nat → Nat)
#check f1 1 -- curried function (Nat → Nat)
#check f1 1 2 -- final type (Nat)

#eval f1 1 2 -- value (3)




/- let binding -/

-- both below are same

def g1 (x: Nat) (f: Nat → Nat) (f': Nat → Nat) (f'': Nat → Nat) :=  f' (f x) + f'' (f x)

def g2 (x: Nat) (f: Nat → Nat) (f': Nat → Nat) (f'': Nat → Nat) :=
  let y := f x;
  f' y + f'' y
