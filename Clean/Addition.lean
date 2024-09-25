import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

variable (N M : ℕ+) (p : ℕ) [Fact p.Prime]

def F p := ZMod p
instance : Field (F p) := ZMod.instField p


def forallList {α : Type} (v : List α) (p : α -> Prop) : Prop :=
  match v with
  | [] => true
  | (x::xs) => p x ∧ forallList xs p

inductive GenericConstraint (N M : ℕ+) : Type
  | Constraint
    -- the list of (multivariate) polynomials that make up the constraint
    (polys : List (MultiPoly N M (F p)))

    -- list of sub-constraints that are instantiated by this constraint
    (subConstraints : List (GenericConstraint N M))

    -- specification
    (spec : Inputs N M (F p) -> Prop)

    -- equivalence theorem
    (equiv : ∀ X, forallList polys (fun constraint => constraint.eval X = 0) ↔ spec X)


namespace Boolean
open Expression
def BooleanConstraint : GenericConstraint p 1 1 :=
  GenericConstraint.Constraint
    [⟨x * (x - 1)⟩]
    []
    (fun inputs => inputs 0 0 = 0 ∨ inputs 0 0 = 1)
    (by
      intro X
      simp [forallList]
      constructor
      · simp [MultiPoly.eval, Expression.eval]
        intro h
        cases h with
        | inl h => left; exact h
        | inr h => right; calc X 0 0
          _ = (X 0 0 + -1 * 1) + 1 := by ring
          _ = 1 := by simp [h]
      · intro h
        simp [MultiPoly.eval, Expression.eval]
        cases h with
        | inl h => left ; exact h
        | inr h => right ; simp [h]
    )
end Boolean


namespace Addition
open Expression
variable {F : Type} [CommRing F]
def x : Expression F := var 0 0
def y : Expression F := var 0 1
def carry : Expression F := var 0 2
def out : Expression F := var 0 3

-- TODO figure out how to instantiate generic constraints with variables
-- TODO add in the type sig of the equivalence the assumptions of the spec of
-- the subconstraints
-- In the end I want to write something like this:
/-
def AdditionConstraint : GenericConstraint p 1 4 :=
  GenericConstraint.Constraint
    [
      ⟨x + y - out - carry*256⟩
    ]
    [
      -- instantiate the BooleanConstraint with the carry variable
      BooleanConstraint carry
    ]
    (fun inputs =>
      have x := inputs 0 0;
      have y := inputs 0 1;
      have carry := inputs 0 2;
      have out := inputs 0 3;
      out = (x + y) % 256 ∧ carry = (x + y) / 256
    )
    (...)
-/

end Addition
