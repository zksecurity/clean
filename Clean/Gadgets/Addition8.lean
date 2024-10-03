import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Clean.Utils.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-
  8-bit addition constraint gadget: the output `out` must be the sum of the
  inputs `x` and `y` modulo 256, and the carry `carry` must be the quotient
  of the sum of `x` and `y` divided by 256.
-/
namespace Addition8
open Expression
variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]
instance : CommRing (F p) := ZMod.commRing p

def circuit (N M : ℕ+) (x y out carry : Expression (F p)) : GenericConstraint p N M :=
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
      (out.val = (x.val + y.val) % 256) ∧ carry.val = (x.val + y.val) / 256)


/-
  First part of the soundness direction: case of zero carry
-/
theorem equiv_mod_256_zero_carry_fw (x y out : F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 ->
    (x + y - out = 0 -> (out.val = (x.val + y.val) % 256 ∧ (x.val + y.val) / 256 = 0)) := by

  intros hx hy hout h
  have not_wrap := FieldUtils.byte_sum_do_not_wrap x y hx hy
  rw [sub_eq_zero] at h
  apply_fun ZMod.val at h
  rw [not_wrap] at h
  rw [←h] at hout
  apply And.intro
  · rw [Nat.mod_eq_of_lt hout]
    apply Eq.symm; assumption
  · apply Nat.div_eq_of_lt; assumption

/-
  Second part of the soundness direction: case of one carry
-/
theorem equiv_mod_256_one_carry_fw (x y out : F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 ->
    x + y - out - 256 = 0 -> (out.val = (x.val + y.val) % 256 ∧ (x.val + y.val) / 256 = 1) := by

  intros hx hy hout h
  have xy_not_wrap := FieldUtils.byte_sum_do_not_wrap x y hx hy
  have out_plus_256_not_wrap := FieldUtils.byte_plus_256_do_not_wrap out hout

  rw [sub_eq_zero] at h
  have h := eq_add_of_sub_eq h
  rw [add_comm 256] at h
  apply_fun ZMod.val at h
  rw [xy_not_wrap, out_plus_256_not_wrap] at h
  have h : (x.val + y.val) - 256 = out.val := Eq.symm (Nat.eq_sub_of_add_eq (Eq.symm h))

  set x := x.val
  set y := y.val
  set out := out.val

  have x_plus_y_overflow_byte : x + y ≥ 256 := by
    have h2 : out + 256 >= 256 := by simp
    rw [←h] at h2
    linarith

  apply And.intro
  · have sub_mod := Nat.mod_eq_sub_mod x_plus_y_overflow_byte
    rw [←h] at hout
    rw [sub_mod, Nat.mod_eq_of_lt hout, h]
  · rw [Nat.div_eq_of_lt_le]
    · rw [←Nat.one_mul 256] at x_plus_y_overflow_byte; assumption
    · simp; exact Nat.add_lt_add hx hy


theorem equiv (N M : ℕ+) (x y out carry: Expression (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carry)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carry)) (fun constraint => constraint.eval X = 0))
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
    · rw [zero_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg] at h
      have thm := equiv_mod_256_zero_carry_fw x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at zero_carry
      rw [ZMod.val_zero] at zero_carry
      rw [← thm.right] at zero_carry
      apply And.intro
      · exact thm.left
      · exact zero_carry
    · rw [one_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg, ←sub_eq_add_neg (x + y)] at h
      have thm := equiv_mod_256_one_carry_fw x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at one_carry
      rw [ZMod.val_one] at one_carry
      rw [← thm.right] at one_carry
      apply And.intro
      · exact thm.left
      · exact one_carry
  · intro h
    have carry? := Nat.lt_or_ge (x.val + y.val) 256
    rcases carry? with sum_lt_256 | sum_ge_256
    · sorry
    · sorry


instance (N M : ℕ+) (x y out carry : Expression (F p)) : Constraint N M p :=
{
  circuit := circuit N M x y out carry,
  spec := spec N M x y out carry,
  equiv := equiv N M x y out carry
}

end Addition8
