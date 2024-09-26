import Clean.GenericExpression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

variable (N : ℕ+) (p : ℕ) [Fact p.Prime]

def F p := ZMod p
instance : Field (F p) := ZMod.instField p
instance : Fintype (F p) := ZMod.fintype p


def forallList {α : Type} (v : List α) (p : α -> Prop) : Prop :=
  match v with
  | [] => true
  | (x::xs) => p x ∧ forallList xs p


inductive GenericConstraint (N : ℕ+) : Type
  | Constraint
    -- the list of (multivariate) polynomials that make up the constraint
    (polys : List (GenericExpression (F p)))

    -- list of sub-constraints that are instantiated by this constraint
    (subConstraints : List (GenericConstraint N))

    -- specification
    (spec : GenericInputs (F p) -> Prop)

    -- equivalence theorem
    (equiv : ∀ X, (forallList polys (fun constraint => constraint.eval X = 0)) ↔ spec X)

    /-
    TODO: We would like to incorporate in the premises the specs of the subconstraints
    but the following is not valid Lean code

    (equiv : (forallList subConstraints (fun c => match c with
      | Constraint polys' subConstraints' spec' equiv' => spec'
    )) -> ∀ X, (forallList polys (fun constraint => constraint.eval X = 0)) ↔ spec X)
    -/
