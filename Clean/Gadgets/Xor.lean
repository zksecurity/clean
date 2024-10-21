import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Boolean
-- Xor constraint gadget: the inputs x, y, z must be a boolean value.
-- z = x xor y

namespace Xor
open Expression
variable {p : ℕ} [Fact p.Prime]

def circuit (N M : ℕ+) (x y z : Expression (F p)) : GenericConstraint p N M :=
  GenericConstraint.mk
    [x + y - (const 2) * x * y - z]
    []
    [ Boolean.circuit N M x,
      Boolean.circuit N M y,
      Boolean.circuit N M z ]

def spec (N M : ℕ+) (x y z: Expression (F p)) : Inputs N M (F p) -> Prop :=
  fun env => (z.eval env).val = (x.eval env).val ^^^ (y.eval env).val

theorem equiv (N M : ℕ+) (x y z: Expression (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y z)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y z)) (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x y z X
    )
  ) := by
    --simp [forallList, fullLookupSet, fullConstraintSet]
    simp [forallList, ByteLookup.lookup]
    intro X

    let equivBoolean_x := Boolean.equiv N M x X
    let equivBoolean_y := Boolean.equiv N M y X
    let equivBoolean_z := Boolean.equiv N M z X
    simp [forallList, Boolean.spec, Expression.eval] at equivBoolean_x equivBoolean_y equivBoolean_z
    simp [Expression.eval]
    rw [equivBoolean_x, equivBoolean_y, equivBoolean_z, spec]
    set x := x.eval X
    set y := y.eval X
    set z := z.eval X

    constructor
    . intro h
      have xor00 : Nat.xor 0 0 = 0 := by rfl
      have xor10 : Nat.xor 1 0 = 1 := by rfl
      have xor01 : Nat.xor 0 1 = 1 := by rfl
      have xor11 : Nat.xor 1 1 = 0 := by rfl
      rcases h with ⟨hxyz, hx_zero | hx_one, hy_zero | hy_one, hz⟩
      . simp [hx_zero, hy_zero] at hxyz
        simp [hx_zero, hy_zero, xor00, hxyz]
      . simp [hx_zero, hy_one] at hxyz
        rw [← sub_eq_add_neg, sub_eq_zero, eq_comm] at hxyz
        simp [hx_zero, hy_one, xor01, ZMod.val_one, hxyz]
      . simp [hx_one, hy_zero] at hxyz
        rw [← sub_eq_add_neg, sub_eq_zero, eq_comm] at hxyz
        simp [hx_one, hy_zero, xor10, ZMod.val_one, hxyz]
      . simp [hx_one, hy_one] at hxyz
        rw [← sub_eq_add_neg, sub_eq_zero, eq_comm] at hxyz
        simp [hx_one, hy_one, ZMod.val_one, xor11, hxyz]
        ring
    -- . intro h
    --   apply And.intro

    --   apply_fun ZMod.val
    --   -- rw [← Nat.xor_eq_zero]
    --   -- rw [← sub_eq_add_neg, eq_comm]
    sorry

end Xor
