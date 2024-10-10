import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


/-
  Equality constraint gadget: x and y must be equal
-/
namespace Equality
open Expression
variable {p : ℕ} [Fact p.Prime]

def circuit (N M : ℕ+) (x y : Expression N M (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [x - y]
    []
    []

def spec (N M : ℕ+) (x y: Expression N M (F p)) : Inputs N M (F p) -> Prop :=
  fun env => (x.eval env) = (y.eval env)

theorem equiv (N M : ℕ+) (x y: Expression N M (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y)) (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x y X
    )
  ) := by

  simp [forallList, fullLookupSet, fullConstraintSet]
  intro X
  simp [Expression.eval]
  rw [←sub_eq_add_neg, sub_eq_zero]
  simp [spec]


instance EqConstraint (N M : ℕ+) (x y: Expression N M (F p)) : Constraint N M p :=
{
  circuit := circuit N M x y,
  spec := spec N M x y,
  equiv := equiv N M x y
}

end Equality
