import Clean.GenericConstraint
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


namespace Boolean

open Expression
variable {p : ℕ} [Fact p.Prime]

-- The nice thing about defining constraints like this is that there is an implicit
-- forall quantifier over all possible input expressions x, so the proof works with every
-- input. This allows for example to instantiate the constraint with a specific input
-- which can be also an expression, for example Boolean.BooleanConstraint (x + y)
def circuit (N M : ℕ+) (x : Expression (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [x * (x - 1)]
    []

def spec (N M : ℕ+) (x: Expression (F p)) : Inputs N M (F p) -> Prop :=
  fun env => x.eval env = 0 ∨ x.eval env = 1

theorem equiv (N M : ℕ+) (x: Expression (F p)) : ∀ X, (forallList (fullConstraintSet (circuit N M x)) (fun constraint => constraint.eval X = 0)) ↔ spec N M x X := by
  intro X
  simp [forallList]
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

instance BooleanConstraint (N M : ℕ+) (x : Expression (F p)) : Constraint N M p :=
  {
    circuit := circuit N M x,
    spec := spec N M x,
    equiv := equiv N M x
  }
end Boolean

/-
namespace Addition

open Expression
variable {p : ℕ} [Fact p.Prime]

def AdditionConstraint (N M : ℕ+) (x y out carry : Expression (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x + y - out - carry * (const 256)
    ]
    [
      Boolean.BooleanConstraint N M carry
    ]
    (fun env =>
      have x := x.eval env;
      have y := y.eval env;
      have out := out.eval env;
      have carry := carry.eval env;
      -- This may be a problematic spec, because there is the hidden assumption
      -- that p > 256*2, because we cast the addition result to ℕ
       (((x + y).val >= 256) -> out = x + y - 256)
       ∧ (((x + y).val < 256) -> out = x + y)
       ∧ carry = (x + y) / 256)
    (sorry)
end Addition
-/
