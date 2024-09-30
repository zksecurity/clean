import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic


namespace Addition8
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
end Addition8
