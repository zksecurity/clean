import Clean.GenericConstraint
import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Clean.Utils.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

/-
  8-bit full adder gadget: the output `out` must be the sum of the
  input bytes `x` and `y` plus the `carry_in` boolean modulo 256,
  and the output carry `carry_out` must be the quotient
  of the sum of `x`, `y` and `carry_in` divided by 256.
-/
namespace Addition8Full
open Expression
variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]

def circuit (N : ℕ+) (M : ℕ) (x y out carry_in carry_out : Expression N M (F p)) : ConstraintGadget p N M :=
  ⟨
    [
      carry_in + x + y - out - carry_out * (const 256)
    ],
    [
      ByteLookup.lookup N M x,
      ByteLookup.lookup N M y,
      ByteLookup.lookup N M out,
    ],
    [
      Boolean.circuit N M carry_in,
      Boolean.circuit N M carry_out
    ]
  ⟩

def spec (N : ℕ+) (M : ℕ) (x y out carry_in carry_out: Expression N M (F p)) : TraceOfLength N M (F p) -> Prop :=
  (fun trace =>
      have x := trace.eval x
      have y := trace.eval y
      have out := trace.eval out
      have carry_in := trace.eval carry_in
      have carry_out := trace.eval carry_out

      -- the output is correct
      (out.val = (carry_in.val + x.val + y.val) % 256)
      -- the output carry is correct
      ∧ carry_out.val = (carry_in.val + x.val + y.val) / 256
      -- the input carry is a free boolean
      ∧ (carry_in = 0 ∨ carry_in = 1))

/-
  First part of the soundness direction: case of zero carry
-/
theorem soundness_zero_carry (x y out carry_in: F p):
    x.val < 256 -> y.val < 256 -> out.val < 256  -> carry_in.val < 2 ->
    (carry_in + x + y - out = 0 -> (out.val = (carry_in.val + x.val + y.val) % 256
    ∧ (carry_in.val + x.val + y.val) / 256 = 0)) := by
  intros hx hy hout hb h
  have not_wrap := FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx hy hb
  rw [sub_eq_zero] at h
  apply_fun ZMod.val at h
  constructor
  · rw [←not_wrap, h, Nat.mod_eq_of_lt hout]
  · apply Nat.div_eq_of_lt
    rw [←not_wrap, h]
    assumption

/-
  Second part of the soundness direction: case of one carry
-/
theorem soundness_one_carry (x y out carry_in: F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 -> carry_in.val < 2 ->
    carry_in + x + y - out - 256 = 0 -> (out.val = (carry_in.val + x.val + y.val) % 256
    ∧ (carry_in.val + x.val + y.val) / 256 = 1) := by

  intros hx hy hout hb h
  have xy_not_wrap := FieldUtils.byte_sum_do_not_wrap x y hx hy
  have not_wrap := FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx hy hb
  have out_plus_256_not_wrap := FieldUtils.byte_plus_256_do_not_wrap out hout

  rw [sub_eq_zero] at h
  apply eq_add_of_sub_eq at h
  rw [add_comm 256] at h
  apply_fun ZMod.val at h
  rw [not_wrap, out_plus_256_not_wrap] at h
  have h : (carry_in.val + x.val + y.val) - 256 = out.val :=
    Eq.symm (Nat.eq_sub_of_add_eq (Eq.symm h))
  have sum_bound := FieldUtils.byte_sum_le_bound x y hx hy
  have sum_le_511 : carry_in.val + (x + y).val ≤ 511 := by
    apply Nat.le_sub_one_of_lt at sum_bound
    apply Nat.le_sub_one_of_lt at hb
    simp at sum_bound
    simp at hb
    apply Nat.add_le_add hb sum_bound
  rw [xy_not_wrap, ←add_assoc] at sum_le_511


  set x := x.val
  set y := y.val
  set carry_in := carry_in.val
  set out := out.val

  have x_plus_y_overflow_byte : carry_in + x + y ≥ 256 := by
    have h2 : out + 256 >= 256 := by simp
    rw [←h] at h2
    linarith

  apply And.intro
  · have sub_mod := Nat.mod_eq_sub_mod x_plus_y_overflow_byte
    rw [←h] at hout
    rw [sub_mod, Nat.mod_eq_of_lt hout, h]
  · rw [Nat.div_eq_of_lt_le]
    · rw [←Nat.one_mul 256] at x_plus_y_overflow_byte; assumption
    · simp
      apply Nat.lt_add_one_of_le
      assumption


theorem equiv (N : ℕ+) (M : ℕ) (x y out carry_in carry_out: Expression N M (F p)) :
  (∀ X,
    (forallList (fullLookupSet (circuit N M x y out carry_in carry_out)) (fun lookup => lookup.prop X))
    -> (
      (forallList (fullConstraintSet (circuit N M x y out carry_in carry_out)) (fun constraint => X.eval constraint = 0))
      ↔
      spec N M x y out carry_in carry_out X
    )
  ) := by

  intro X
  simp [forallList, ByteLookup.lookup]
  let equivBoolean := Boolean.equiv N M carry_in X
  simp [forallList, Boolean.spec] at equivBoolean
  rw [equivBoolean]

  let equivBoolean := Boolean.equiv N M carry_out X
  simp [forallList, Boolean.spec] at equivBoolean
  rw [equivBoolean, spec]

  simp [TraceOfLength.eval]
  set x := X.eval x
  set y := X.eval y
  set out := X.eval out
  set carry_in := X.eval carry_in
  set carry_out := X.eval carry_out

  intros hx_byte hy_byte hout_byte
  constructor

  -- soundness
  · intro h
    have ⟨h, ⟨carry_in_bool, carry_out_bool⟩⟩ := h
    simp [carry_in_bool]
    have carry_in_bound := FieldUtils.boolean_le_2 carry_in carry_in_bool

    rcases carry_out_bool with zero_carry | one_carry
    · rw [zero_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg] at h
      have thm := soundness_zero_carry x y out carry_in hx_byte hy_byte hout_byte carry_in_bound h
      apply_fun ZMod.val at zero_carry
      rw [ZMod.val_zero, ← thm.right] at zero_carry
      apply And.intro
      · exact thm.left
      · exact zero_carry
    · rw [one_carry] at h
      simp [ZMod.val_add] at h
      rw [←sub_eq_add_neg, ←sub_eq_add_neg (carry_in + x + y)] at h
      have thm := soundness_one_carry x y out carry_in hx_byte hy_byte hout_byte carry_in_bound h
      apply_fun ZMod.val at one_carry
      rw [ZMod.val_one, ← thm.right] at one_carry
      apply And.intro
      · exact thm.left
      · exact one_carry

  -- completeness
  · intro h
    have carry? := Nat.lt_or_ge (carry_in.val + x.val + y.val) 256
    rcases carry? with sum_lt_256 | sum_ge_256
    · have h1 := h.left
      have h2 := h.right.left
      have h3 := h.right.right
      simp [h3]
      have carry_in_bound := FieldUtils.boolean_le_2 carry_in h3
      rw [(Nat.mod_eq_iff_lt (by linarith)).mpr sum_lt_256] at h1
      rw [←FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx_byte hy_byte carry_in_bound] at h1
      rw [Nat.div_eq_of_lt sum_lt_256] at h2
      simp at h2
      rw [h2]; simp
      rw [←sub_eq_add_neg, sub_eq_zero]
      apply_fun ZMod.val
      · exact Eq.symm h1
      · apply ZMod.val_injective
    · have ⟨h1, ⟨h2, h3⟩⟩ := h
      have carry_in_bound := FieldUtils.boolean_le_2 carry_in h3
      have sum_bound := FieldUtils.byte_sum_le_bound x y hx_byte hy_byte
      have sum_le_511 : carry_in.val + (x + y).val ≤ 511 := by
        apply Nat.le_sub_one_of_lt at sum_bound
        apply Nat.le_sub_one_of_lt at carry_in_bound
        simp at sum_bound
        simp at carry_in_bound
        apply Nat.add_le_add carry_in_bound sum_bound
      rw [FieldUtils.byte_sum_do_not_wrap x y hx_byte hy_byte, ←add_assoc] at sum_le_511

      have sum_le_512 := Nat.add_lt_add hx_byte hy_byte
      simp at sum_le_512
      have div_one : (carry_in.val + x.val + y.val) / 256 = 1 := by
        apply Nat.div_eq_of_lt_le
        · simp; exact sum_ge_256
        · simp; apply Nat.lt_add_one_of_le; assumption
      have val_one_is_one := FieldUtils.val_lt_p 1 (Nat.lt_trans (by norm_num) p_large_enough.elim)
      rw [div_one] at h2
      rw [← val_one_is_one] at h2
      simp at h2
      have carry_one : carry_out = 1 := (Function.Injective.eq_iff (ZMod.val_injective p)).mp h2
      rw [carry_one]
      simp [h3]
      rw [←sub_eq_add_neg, sub_eq_zero, add_eq_of_eq_sub]
      rw [sub_eq_add_neg, add_comm 256, ← sub_eq_iff_eq_add]
      simp
      have modulo_definition_div := Nat.mod_add_div (carry_in.val + x.val + y.val) 256
      rw [div_one] at modulo_definition_div
      simp at modulo_definition_div
      apply_fun ZMod.val

      · have not_wrap := FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx_byte hy_byte carry_in_bound
        rw [←not_wrap] at h1
        rw [←not_wrap] at sum_ge_256
        have val_256_is_256 := FieldUtils.val_lt_p 256 (Nat.lt_trans (by norm_num) p_large_enough.elim)
        rw [←val_256_is_256] at sum_ge_256
        have sub_256_val : ((carry_in + x + y) - 256).val = (carry_in + x+y).val - (256 : F p).val :=
          ZMod.val_sub sum_ge_256
        simp at val_256_is_256
        rw [sub_256_val, not_wrap, val_256_is_256, ← modulo_definition_div, ←not_wrap]
        simp; exact (Eq.symm h1)
      · apply ZMod.val_injective


instance (N M : ℕ+) (x y out carry_in carry_out : Expression N M (F p)) : Constraint N M p :=
{
  circuit := circuit N M x y out carry_in carry_out,
  spec := spec N M x y out carry_in carry_out,
  equiv := equiv N M x y out carry_in carry_out
}

end Addition8Full
