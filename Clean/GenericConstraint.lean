import Clean.Utils.Field
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section
variable (N : ℕ+) (p : ℕ) [Fact p.Prime]

/-
  A LookupArgument is an assumption on the inputs to a constraint. For now this is represented
  as a function that takes the inputs and returns a Prop.
  TODO: replace with an actual structure, maybe a class as below for Constraint
-/
structure LookupArgument (N M : ℕ+) where
  prop : Inputs N M (F p) -> Prop

/-
  A GenericConstraint is a constraint that can be instantiated with a specific set of inputs.
  It is composed of
  - polys: the list of (multivariate) polynomials that make up the constraint, implicitly the
        constraint holds if all of these polynomials evaluate to 0
  - lookups: the list of lookup arguments that are assumed to hold for the inputs
  - subConstraints: the list of sub-constraints that are instantiated by this constraint
-/
inductive GenericConstraint (N M : ℕ+) where
    | mk
    (polys : List (Expression N M (F p)))
    (lookups : List (LookupArgument p N M))
    (subConstraints : List (GenericConstraint N M))

-- compute the full set of constraints that are implied by this constraint
def fullConstraintSet {N M : ℕ+} {p : ℕ} [Fact p.Prime] (x : GenericConstraint p N M) : List (Expression N M (F p)) :=
  match x with
    | GenericConstraint.mk polys _ subConstraints => polys ++ (foldl [] subConstraints)
where
  foldl : List (Expression N M (F p)) → List (GenericConstraint p N M) → List (Expression N M (F p))
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullConstraintSet t) ts

-- compute the full set of lookup arguments that are implied by this constraint
def fullLookupSet {N M : ℕ+} {p : ℕ} [Fact p.Prime] (x : GenericConstraint p N M) : List (LookupArgument p N M) :=
  match x with
    | GenericConstraint.mk _ lookups subConstraints => lookups ++ (foldl [] subConstraints)
where
  foldl : List (LookupArgument p N M) → List (GenericConstraint p N M) → List (LookupArgument p N M)
    | arr, [] => arr
    | arr, (t :: ts) => foldl (arr ++ fullLookupSet t) ts

def forallList {α : Type} (v : List α) (p : α -> Prop) : Prop :=
  match v with
  | [] => true
  | (x::xs) => p x ∧ forallList xs p

/-
  A Constraint is a typeclass that packages the definition of the circuit together with its higher
  level specification.
  The equivalence theorem states that the full set of constraints implied by the circuit
  is satisfied if and only if the spec is satisfied, given as assumptions the lookups.
-/
class Constraint (N M : ℕ+) (p : ℕ) [Fact p.Prime] :=
    -- the constraints
    (circuit : GenericConstraint p N M)

    -- specification
    (spec : Inputs N M (F p) -> Prop)

    -- equivalence theorem
    (equiv :
      (∀ X,
        (forallList (fullLookupSet circuit) (fun lookup => lookup.prop X))
        -> (
          (forallList (fullConstraintSet circuit) (fun constraint => constraint.eval X = 0))
          ↔
          spec X
        )
      ))

end
