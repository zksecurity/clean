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

-- TODO: replace with an actual structure, maybe a class as below for Constraint
structure LookupArgument (N M : ℕ+) where
  prop : Inputs N M (F p) -> Prop

inductive GenericConstraint (N M : ℕ+) where
    | mk
    -- the list of (multivariate) polynomials that make up the constraint
    (polys : List (Expression (F p)))

    -- list of lookup arguments that are used in the constraint
    (lookups : List (LookupArgument p N M))

    -- list of sub-constraints that are instantiated by this constraint
    (subConstraints : List (GenericConstraint N M))


-- compute the full set of constraints that are implied by this constraint
def fullConstraintSet {N M : ℕ+} {p : ℕ} [Fact p.Prime] (x : GenericConstraint p N M) : List (Expression (F p)) :=
  match x with
    | GenericConstraint.mk polys _ subConstraints => polys ++ (foldl [] subConstraints)
where
  foldl : List (Expression (F p)) → List (GenericConstraint p N M) → List (Expression (F p))
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullConstraintSet t) ts


def fullLookupSet {N M : ℕ+} {p : ℕ} [Fact p.Prime] (x : GenericConstraint p N M) : List (LookupArgument p N M) :=
  match x with
    | GenericConstraint.mk _ lookups subConstraints => lookups ++ (foldl [] subConstraints)
where
  foldl : List (LookupArgument p N M) → List (GenericConstraint p N M) → List (LookupArgument p N M)
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullLookupSet t) ts


class Constraint (N M : ℕ+) (p : ℕ) [Fact p.Prime] :=
    -- the constraints
    (circuit : GenericConstraint p N M)

    -- specification
    (spec : Inputs N M (F p) -> Prop)

    -- equivalence theorem, with lookup props into the assumptions
    (equiv :
      (∀ X,
        (forallList (fullLookupSet circuit) (fun lookup => lookup.prop X))
        -> (
          (forallList (fullConstraintSet circuit) (fun constraint => constraint.eval X = 0))
          ↔
          spec X
        )
      ))
