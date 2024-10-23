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

def circuit (N : ℕ+) (M : ℕ) (x y out carry : Expression N M (F p)) : ConstraintGadget p N M :=
  ⟨
    [
      x + y - out - carry * (const 256)
    ],
    [
      ByteLookup.lookup N M x,
      ByteLookup.lookup N M y,
      ByteLookup.lookup N M out,
    ],
    [
      Boolean.circuit N M carry
    ]
  ⟩

def spec (N : ℕ+) (M : ℕ) (x y out carry: Expression N M (F p)) : TraceOfLength N M (F p) -> Prop :=
  (fun trace =>
      have x := trace.eval x;
      have y := trace.eval y;
      have out := trace.eval out;
      have carry := trace.eval carry;
      (out.val = (x.val + y.val) % 256) ∧ carry.val = (x.val + y.val) / 256)


/-
  First part of the soundness direction: case of zero carry
-/
theorem soundness_zero_carry (x y out : F p):
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
theorem soundness_one_carry (x y out : F p):
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


theorem equiv (N : ℕ+) (M : ℕ) (x y out carry: Expression N M (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carry)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carry)) (fun constraint => X.eval constraint = 0))
      ↔
      spec N M x y out carry X
    )
  ) := by

  intro X
  simp [forallList, ByteLookup.lookup]
  let equivBoolean := Boolean.equiv N M carry X
  simp [forallList, Boolean.spec] at equivBoolean
  rw [equivBoolean, spec]

  simp [TraceOfLength.eval]
  set x := X.eval x
  set y := X.eval y
  set out := X.eval out
  set carry := X.eval carry

  intro hx_byte
  intro hy_byte
  intro hout_byte
  constructor

  -- soundness
  · intro h
    rcases (And.right h) with zero_carry | one_carry
    · rw [zero_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg] at h
      have thm := soundness_zero_carry x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at zero_carry
      rw [ZMod.val_zero, ← thm.right] at zero_carry
      apply And.intro
      · exact thm.left
      · exact zero_carry
    · rw [one_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg, ←sub_eq_add_neg (x + y)] at h
      have thm := soundness_one_carry x y out hx_byte hy_byte hout_byte h
      apply_fun ZMod.val at one_carry
      rw [ZMod.val_one, ← thm.right] at one_carry
      apply And.intro
      · exact thm.left
      · exact one_carry

  -- completeness
  · intro h
    have carry? := Nat.lt_or_ge (x.val + y.val) 256
    rcases carry? with sum_lt_256 | sum_ge_256

    -- first case: x + y <= 256, carry = 0
    · have h1 := h.left; have h2 := h.right
      rw [(Nat.mod_eq_iff_lt (by linarith)).mpr sum_lt_256] at h1
      rw [←FieldUtils.byte_sum_do_not_wrap x y hx_byte hy_byte] at h1
      rw [Nat.div_eq_of_lt sum_lt_256] at h2
      simp at h2
      rw [h2]; simp
      rw [←sub_eq_add_neg, sub_eq_zero]
      apply_fun ZMod.val
      · exact Eq.symm h1
      · apply ZMod.val_injective

    -- second case: x + y > 256, carry = 1
    · have h1 := h.left; have h2 := h.right
      have sum_le_512 := Nat.add_lt_add hx_byte hy_byte
      simp at sum_le_512
      have div_one : (x.val + y.val) / 256 = 1 := by
        apply Nat.div_eq_of_lt_le
        · simp; exact sum_ge_256
        · simp; exact sum_le_512
      have val_one_is_one := FieldUtils.val_lt_p 1 (Nat.lt_trans (by norm_num) p_large_enough.elim)
      rw [div_one] at h2
      rw [← val_one_is_one] at h2
      simp at h2
      have carry_one : carry = 1 := (Function.Injective.eq_iff (ZMod.val_injective p)).mp h2
      rw [carry_one]
      simp
      rw [←sub_eq_add_neg, sub_eq_zero, add_eq_of_eq_sub]
      simp
      rw [add_comm 256, ← sub_eq_iff_eq_add]
      have modulo_definition_div := Nat.mod_add_div (x.val + y.val) 256
      rw [div_one] at modulo_definition_div
      simp at modulo_definition_div
      apply_fun ZMod.val
      · have xy_not_wrap := FieldUtils.byte_sum_do_not_wrap x y hx_byte hy_byte
        rw [←xy_not_wrap] at h1
        rw [←xy_not_wrap] at sum_ge_256
        have val_256_is_256 := FieldUtils.val_lt_p 256 (Nat.lt_trans (by norm_num) p_large_enough.elim)
        rw [←val_256_is_256] at sum_ge_256
        have sub_256_val : ((x + y) - 256).val = (x+y).val - (256 : F p).val  := ZMod.val_sub sum_ge_256
        simp at val_256_is_256
        rw [sub_256_val, xy_not_wrap, val_256_is_256, ← modulo_definition_div, ←xy_not_wrap]
        simp; exact (Eq.symm h1)
      · apply ZMod.val_injective


instance (N M : ℕ+) (x y out carry : Expression N M (F p)) : Constraint N M p :=
{
  circuit := circuit N M x y out carry,
  spec := spec N M x y out carry,
  equiv := equiv N M x y out carry
}

end Addition8
