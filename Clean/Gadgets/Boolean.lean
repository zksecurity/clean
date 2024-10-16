import Clean.GenericConstraint
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


/-
  Booleanity constraint gadget: the input x must be a boolean value, i.e. x = 0 or x = 1
-/
namespace Boolean
open Expression
variable {p : ℕ} [Fact p.Prime]

def circuit (N : ℕ+) (M : ℕ) (x : Expression N M (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [x * (x - 1)]
    []
    []

def spec (N : ℕ+) (M : ℕ) (x: Expression N M (F p)) : InputsOfLength N (F p) M -> Prop :=
  fun env => env.eval x = 0 ∨ env.eval x = 1

theorem equiv (N : ℕ+) (M : ℕ) (x: Expression N M (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x)) (fun constraint => X.eval constraint = 0))
      ↔
      spec N M x X
    )
  ) := by

  simp [forallList, fullLookupSet, fullConstraintSet]
  intro X
  constructor
  · intro h
    simp [InputsOfLength.eval] at h
    simp [spec]
    cases h with
    | inl h => left; exact h
    | inr h => right; calc
          X.eval x = X.eval x + (-1) + 1 := by ring
          _ = 1 := by simp [h]
  · intro h
    simp [InputsOfLength.eval]
    simp [spec] at h
    cases h with
    | inl h => left ; exact h
    | inr h => right ; simp [h]


instance BooleanConstraint (N : ℕ+) (M : ℕ) (x : Expression N M (F p)) : Constraint N M p :=
{
  circuit := circuit N M x,
  spec := spec N M x,
  equiv := equiv N M x
}

end Boolean
