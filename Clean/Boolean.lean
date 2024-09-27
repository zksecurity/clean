import Clean.GenericConstraint
import Clean.Expression
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


namespace ByteLookup
open Expression
variable {p : ℕ} [Fact p.Prime]

def lookup (N M : ℕ+) (x : Expression (F p)) : LookupArgument p N M :=
  {
    -- NOTE: is this correct? Not for a general prime p I think
    prop := fun env => (x.eval env).val < 256
  }

end ByteLookup


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
    []

def spec (N M : ℕ+) (x: Expression (F p)) : Inputs N M (F p) -> Prop :=
  fun env => x.eval env = 0 ∨ x.eval env = 1

theorem equiv (N M : ℕ+) (x: Expression (F p)) :
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

instance BooleanConstraint (N M : ℕ+) (x : Expression (F p)) : Constraint N M p :=
  {
    circuit := circuit N M x,
    spec := spec N M x,
    equiv := equiv N M x
  }
end Boolean

namespace Addition

open Expression
variable {p : ℕ} [Fact p.Prime]

def AdditionConstraint (N M : ℕ+) (x y out carry : Expression (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x + y - out - carry * (const 256)
    ]
    [
      ByteLookup.lookup N M x,
      ByteLookup.lookup N M y,
      ByteLookup.lookup N M out,
    ]
    [
      Boolean.circuit N M carry
    ]

def spec (N M : ℕ+) (x y out carry: Expression (F p)) : Inputs N M (F p) -> Prop :=
  (fun env =>
      have x := x.eval env;
      have y := y.eval env;
      have out := out.eval env;
      have carry := carry.eval env;
      -- This may be a problematic spec, because we cast the addition result to ℕ
      -- modulo reduction is not defined over (F p)
       (out.val = (x.val + y.val) % 256) ∧ carry.val = (x.val + y.val) / 256)


theorem equiv (N M : ℕ+) (x y out carry: Expression (F p)) :
  (∀ X,
    (forallList (fullLookupSet (AdditionConstraint N M x y out carry)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (AdditionConstraint N M x y out carry)) (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x y out carry X
    )
  ) := by

  intro X
  simp [forallList, ByteLookup.lookup]
  let equivBoolean := Boolean.equiv N M carry X
  simp [forallList, Boolean.spec] at equivBoolean
  rw [equivBoolean, spec]

  simp [eval]

  -- simplify the goal getting rid of evals
  set x := x.eval X
  set y := y.eval X
  set out := out.eval X
  set carry := carry.eval X

  intro hx_byte
  intro hy_byte
  intro hout_byte

  constructor
  · intro h
    rcases (And.right h) with zero_carry | one_carry
    · rw [zero_carry]
      simp [ZMod.val_add]
      apply And.intro
      rw [zero_carry] at h
      simp [ZMod.val_add] at h
      · sorry
      · sorry
    · sorry
  · sorry
end Addition
