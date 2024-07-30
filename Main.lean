import «LearningLean»

abbrev N := Nat

-- def hello := "Gregor"

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

def add1 (x : N) : N :=
  x + 1

#eval add1 10

def maxi (x y : Nat) :=
  if x > y then x else y

#eval maxi 10 10

#check 0.0

structure Complex where
  x : Float
  y : Float
deriving Repr

def Complex.map (f : Float -> Float) (c : Complex) : Complex :=
  { x := f c.x, y := f c.y }

def c : Complex := Complex.mk 0.1 0.2

#eval Complex.map Float.exp { c with x := 0. }

inductive Natural where
  | zero : Natural
  | after (n : Natural) : Natural
deriving Repr

def Positive := { n : Natural // (∃ m : Natural, n = Natural.after m) }

namespace Natural
  def ofNat (n: Nat) : Natural :=
    match n with
    | 0 => zero
    | n + 1 => after (ofNat n)

  def one := after zero

  def isZero (n : Natural) :=
    match n with
    | zero => true
    | after _ => false

  def plus2 (n : Natural) :=
    Natural.after (Natural.after n)

  def pred : (n : Positive) -> Natural
    | ⟨zero, h⟩ =>
      have fls : False :=
        match h with
        | ⟨_, h⟩ => Natural.noConfusion h
      absurd fls id
    | ⟨after m, _⟩ => m
end Natural

-- can't be synthesized
def Positive.from (n: Natural) { m: Natural } { h: n = Natural.after m } : Positive :=
  ⟨n, ⟨m, h⟩⟩


instance : OfNat Natural n where
  ofNat := Natural.ofNat n

-- #eval Positive.from (5: Natural)

#eval Natural.pred ⟨4, ⟨3, rfl⟩⟩

#eval Natural.plus2 Natural.one

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def head : Vector α (m+1) → α
  | cons a as => a

end Vector

def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

def f' := Quot.lift f f_respects

#check (f' : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : f' (Quot.mk mod7Rel a) = f a :=
  rfl

def Field (n: Nat) := Quot.mk mod7Rel n

#check (Field 14)

#eval f' (Field 14)
