import Clean.Expression
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


inductive GenericConstraint (N M : ℕ+) where
    | mk
    -- the list of (multivariate) polynomials that make up the constraint
    (polys : List (Expression (F p)))

    -- list of sub-constraints that are instantiated by this constraint
    (subConstraints : List (GenericConstraint N M))


-- compute the full set of constraints that are implied by this constraint
def fullConstraintSet {N M : ℕ+} {p : ℕ} [Fact p.Prime] (x : GenericConstraint p N M) : List (Expression (F p)) :=
  match x with
    | GenericConstraint.mk polys subConstraints => polys ++ (foldl [] subConstraints)
where
  foldl : List (Expression (F p)) → List (GenericConstraint p N M) → List (Expression (F p))
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullConstraintSet t) ts


class Constraint (N M : ℕ+) (p : ℕ) [Fact p.Prime] :=
    -- the constraints
    (circuit : GenericConstraint p N M)

    -- specification
    (spec : Inputs N M (F p) -> Prop)

    -- equivalence theorem
    (equiv : ∀ X, (forallList (fullConstraintSet circuit) (fun constraint => constraint.eval X = 0)) ↔ spec X)
