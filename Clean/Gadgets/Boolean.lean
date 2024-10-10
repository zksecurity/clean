import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


/-
  Booleanity constraint gadget: the input x must be a boolean value, i.e. x = 0 or x = 1
-/
namespace Boolean
open Expression
variable {p : ℕ} [Fact p.Prime]

def circuit (N M : ℕ+) (x : Expression N M (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [x * (x - 1)]
    []
    []

def spec (N M : ℕ+) (x: Expression N M (F p)) : Inputs N M (F p) -> Prop :=
  fun env => x.eval env = 0 ∨ x.eval env = 1

theorem equiv (N M : ℕ+) (x: Expression N M (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x)) (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x X
    )
  ) := by

  simp [forallList, fullLookupSet, fullConstraintSet]
  intro X
  constructor
  · intro h
    simp [Expression.eval] at h
    simp [spec]
    cases h with
    | inl h => left; exact h
    | inr h => right; calc
          eval X x = eval X x + (-1) + 1 := by ring
          _ = 1 := by simp [h]
  · intro h
    simp [Expression.eval]
    simp [spec] at h
    cases h with
    | inl h => left ; exact h
    | inr h => right ; simp [h]


instance BooleanConstraint (N M : ℕ+) (x : Expression N M (F p)) : Constraint N M p :=
{
  circuit := circuit N M x,
  spec := spec N M x,
  equiv := equiv N M x
}

end Boolean
