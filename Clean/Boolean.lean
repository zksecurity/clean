import Clean.GenericConstraint
import Clean.GenericExpression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


namespace Boolean

open GenericExpression
variable {p : ℕ} [Fact p.Prime]

-- The nice thing about defining constraints like this is that there is an implicit
-- forall quantifier over all possible input expressions x, so the proof works with every
-- input. This allows for example to instantiate the constraint with a specific input
-- which can be also an expression, for example Boolean.BooleanConstraint (x + y)
def BooleanConstraint (x : GenericExpression (F p)) : GenericConstraint p 1 :=
  GenericConstraint.Constraint
    [x * (x - 1)]
    []
    (fun env => x.eval env = 0 ∨ x.eval env = 1)
    (by
      intro X
      simp [forallList]
      constructor
      · simp [GenericExpression.eval]
        intro h
        cases h with
        | inl h => left; exact h
        | inr h => right; calc
          eval X x = eval X x + (-1) + 1 := by ring
          _ = 1 := by simp [h]
      · intro h
        simp [GenericExpression.eval]
        cases h with
        | inl h => left ; exact h
        | inr h => right ; simp [h]
    )
end Boolean


namespace Addition

open GenericExpression
variable {p : ℕ} [Fact p.Prime]

def AdditionConstraint (x y out carry : GenericExpression (F p)) : GenericConstraint p 1 :=
  GenericConstraint.Constraint
    [
      x + y - out - carry * (const 256)
    ]
    [
      Boolean.BooleanConstraint carry
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
