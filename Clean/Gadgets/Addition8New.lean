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

-- could use nats as expressions but seems to slightly complicate proofs
instance {N: ℕ+} {M n : ℕ} : OfNat (Expression N M (F p)) n where
  ofNat := const (OfNat.ofNat n : (Fin p))

variable (N : ℕ+) (M : ℕ)

def assumptions (x y z : Expression N M (F p)) := [
  ByteLookup.lookup N M x,
  ByteLookup.lookup N M y,
  ByteLookup.lookup N M z,
]

def circuit (N : ℕ+) (M : ℕ) (x y out carry : Expression N M (F p)) : ConstraintGadget p N M :=
  ⟨
    [
      x + y - out - carry * (const 256)
    ],
    assumptions N M x y out,
    [
      Boolean.circuit N M carry
    ]
  ⟩


def spec (N : ℕ+) (M : ℕ) (x y z: Expression N M (F p)) : TraceOfLength N M (F p) -> Prop :=
  fun trace =>
    have x := trace.eval x
    have y := trace.eval y
    have z := trace.eval z
    z.val = (x.val + y.val) % 256

theorem equiv (N : ℕ+) (M : ℕ) (x y out: Expression N M (F p)) :
  (∀ X,
    (forallList (assumptions N M x y out) (fun lookup => lookup.prop X))
    -> (
      (∃ carry, constraints_hold (circuit N M x y out carry) X)
      ↔
      spec N M x y out X
    )
  ) := by

  intro X
  simp [constraints_hold, forallList, ByteLookup.lookup]
  simp [TraceOfLength.eval, spec]
  intro hx_byte
  intro hy_byte
  intro hout_byte
  set x := X.eval x
  set y := X.eval y
  set out := X.eval out

  -- preliminaries
  have no_wrap_xy : (x + y).val = x.val + y.val := by
    rw [ZMod.val_add_of_lt]
    linarith [hx_byte, hy_byte, p_large_enough.elim]

  have val_self : (256 : ZMod p).val = 256 := ZMod.val_natCast_of_lt (by linarith [p_large_enough.elim])

  have no_wrap_out : (out + 256).val = out.val + 256 := by
    rw [ZMod.val_add_of_lt, val_self]
    linarith [hout_byte, p_large_enough.elim]

  constructor
  -- soundness
  · rintro ⟨ carry, h ⟩
    set carry := X.eval carry
    rcases (And.right h) with zero_carry | one_carry
    -- carry = 0
    · rw [zero_carry] at h
      simp [←sub_eq_add_neg] at h
      rw [←Nat.mod_eq_of_lt hout_byte]
      have : out = x + y := calc
        _ = 0 + out := by ring
        _ = x + y - out + out := by rw [h]
        _ = x + y := by ring
      rw [this, no_wrap_xy]
    -- carry = 1
    · have one_carry': carry = 1 := calc
        _ = carry - 0 := by ring
        _ = carry - (carry + -1) := by rw [one_carry]
        _ = 1 := by ring
      rw [one_carry'] at h
      simp [ZMod.val_add] at h
      rw [← Nat.mod_eq_of_lt hout_byte]
      rw [← no_wrap_xy]
      have : x + y = out + 256 := calc
        _ = x + y + -out + -256 + out + 256 := by ring
        _ = 0 + out + 256 := by rw [h]
        _ = _ := by ring
      rw [this, no_wrap_out]
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

  -- completeness
  · intro h
    have carry? := Nat.lt_or_ge (x.val + y.val) 256
    rcases carry? with sum_lt_256 | sum_ge_256

    -- first case: x + y <= 256, carry = 0
    · use 0
      simp [TraceOfLength.eval]
      rw [(Nat.mod_eq_iff_lt (by linarith)).mpr sum_lt_256, ← no_wrap_xy] at h
      rw [←sub_eq_add_neg, sub_eq_zero]
      apply_fun ZMod.val
      · symm; exact h
      · apply ZMod.val_injective

    -- second case: x + y > 256, carry = 1
    · use 1
      simp [TraceOfLength.eval]
      have one_lt : 1 < p := by linarith [p_large_enough.elim]
      rw [Nat.mod_eq_of_lt one_lt]
      have one_val : ((1 : ℕ) : ZMod p).val = 1 := ZMod.val_natCast_of_lt one_lt
      simp [one_val]
      suffices g : x + y = out + 256 from calc x + y + -out + -256
        _ = out + 256 + -out + -256 := by rw [g]
        _ = 0 := by ring

      have sum_le_512 := Nat.add_lt_add hx_byte hy_byte
      simp at sum_le_512
      have div_one : (x.val + y.val) / 256 = 1 := by
        apply Nat.div_eq_of_lt_le
        · simp; exact sum_ge_256
        · simp; exact sum_le_512
      have modulo_definition_div := Nat.mod_add_div (x.val + y.val) 256
      rw [← h, div_one] at modulo_definition_div
      simp at modulo_definition_div
      symm
      apply_fun ZMod.val
      · rw [no_wrap_xy, no_wrap_out]
        exact modulo_definition_div
      · apply ZMod.val_injective

end Addition8
