import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Addition32
open Expression

variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 2 ^ 33)]

-- Addition of elements from GL(2 ^ 32) as
-- x = x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃ * 2 ^ 24 : ∀ i xi < 2 ^ 8


def lookup (N M : ℕ+) (x : Expression (F p)) (n : ℕ+) : LookupArgument p N M :=
  {
    prop := fun env => (x.eval env).val < n
  }

def AdditionConstraint (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
: GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x₀ + y₀ - z₀ - c₀ * const (2 ^ 8),
      x₁ + y₁ + c₀ - z₁ - c₁ * const (2 ^ 8),
      x₂ + y₂ + c₁ - z₂ - c₂ * const (2 ^ 8),
      x₃ + y₃ + c₂ - z₃ - c₃ * const (2 ^ 8)
    ]

    [
      lookup N M x₀ (2 ^ 8), lookup N M x₁ (2 ^ 8), lookup N M x₂ (2 ^ 8), lookup N M x₃ (2 ^ 8),
      lookup N M y₀ (2 ^ 8), lookup N M y₁ (2 ^ 8), lookup N M y₂ (2 ^ 8), lookup N M y₃ (2 ^ 8),
      lookup N M z₀ (2 ^ 8), lookup N M z₁ (2 ^ 8), lookup N M z₂ (2 ^ 8), lookup N M z₃ (2 ^ 8),
    ]

    [
      Boolean.circuit N M c₀,
      Boolean.circuit N M c₁,
      Boolean.circuit N M c₂,
      Boolean.circuit N M c₃
    ]

def spec (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
  : Inputs N M (F p) -> Prop :=
    (fun env =>
      have x := (x₀.eval env) + (x₁.eval env) * 2 ^ 8 + (x₂.eval env) * 2 ^ 16 + (x₃.eval env) * 2 ^ 24;
      have y := (y₀.eval env) + (y₁.eval env) * 2 ^ 8 + (y₂.eval env) * 2 ^ 16 + (y₃.eval env) * 2 ^ 24;
      have z := (z₀.eval env) + (z₁.eval env) * 2 ^ 8 + (z₂.eval env) * 2 ^ 16 + (z₃.eval env) * 2 ^ 24;
      have c₃ := c₃.eval env;
      z.val = (x.val + y.val) % 2 ^ 32
      ∧ c₃.val  = (x.val + y.val) / 2 ^ 32
    )

theorem val_dist1 (x y z : F p) : (x + y + z).val = (x.val + y.val + z.val) % p := by
  rw [ZMod.val_add, ZMod.val_add x y, add_comm, Nat.add_mod_mod, add_comm]

theorem val_dist2 (x y z w : F p) : (x + y + z + w).val = (x.val + y.val + z.val + w.val) % p := by
  rw [val_dist1, ZMod.val_add, add_assoc, add_comm, Nat.add_mod_mod, ← add_assoc]
  ring

theorem addition_bound (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : F p) :
  x₀.val < 2 ^ 8 -> x₁.val < 2 ^ 8 -> x₂.val < 2 ^ 8 -> x₃.val < 2 ^ 8 ->
  y₀.val < 2 ^ 8 -> y₁.val < 2 ^ 8 -> y₂.val < 2 ^ 8 -> y₃.val < 2 ^ 8 ->
  (x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃  * 2 ^ 24).val +
  (y₀ + y₁ * 2 ^ 8 + y₂ * 2 ^ 16 + y₃  * 2 ^ 24).val < 2 ^ 33 := by

    have le_256_p : 256 < p := by linarith [p_large_enough.1]
    have le_65536_p : 65536 < p := by linarith [p_large_enough.1]
    have le_16777216_p : 16777216 < p := by linarith [p_large_enough.1]

    have val_256_is_256 : (256 : F p).val = 256 := ZMod.val_natCast_of_lt le_256_p
    have val_65536_is_65536 : (65536 : F p).val = 65536 := ZMod.val_natCast_of_lt le_65536_p
    have val_16777216_is_16777216 : (16777216 : F p).val = 16777216 := ZMod.val_natCast_of_lt le_16777216_p

    intro hx₀ hx₁ hx₂ hx₃ hy₀ hy₁ hy₂ hy₃
    rw [val_dist2, val_dist2,  Nat.mod_eq_of_lt,  Nat.mod_eq_of_lt]
    repeat' rw [ZMod.val_mul, Nat.mod_eq_of_lt]
    norm_num

    rw [val_256_is_256, val_65536_is_65536, val_16777216_is_16777216]
    linarith

    all_goals sorry




theorem equiv (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p)) :
  (∀ X,
    (forallList
         (fullLookupSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
         (fun lookup => lookup.prop X))
    -> (
      (forallList
         (fullConstraintSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
         (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ X
    )
  ) := by
    intro X
    simp [forallList, ByteLookup.lookup]
    let equivBoolean0 := Boolean.equiv N M c₀ X
    let equivBoolean1 := Boolean.equiv N M c₁ X
    let equivBoolean2 := Boolean.equiv N M c₂ X
    let equivBoolean3 := Boolean.equiv N M c₃ X
    simp [forallList, Boolean.spec] at equivBoolean0
    simp [forallList, Boolean.spec] at equivBoolean1
    simp [forallList, Boolean.spec] at equivBoolean2
    simp [forallList, Boolean.spec] at equivBoolean3
    rw [equivBoolean0, equivBoolean1, equivBoolean2, equivBoolean3, spec]

    simp [eval]

    intro hx0_byte hx1_byte hx2_byte hx3_byte
          hy0_byte hy1_byte hy2_byte hy3_byte
          hz0_byte hz1_byte hz2_byte hz3_byte

    simp [lookup] at hx0_byte hx1_byte hx2_byte hx3_byte
                     hy0_byte hy1_byte hy2_byte hy3_byte
                     hz0_byte hz1_byte hz2_byte hz3_byte

    set x₀ := x₀.eval X
    set x₁ := x₁.eval X
    set x₂ := x₂.eval X
    set x₃ := x₃.eval X

    set y₀ := y₀.eval X
    set y₁ := y₁.eval X
    set y₂ := y₂.eval X
    set y₃ := y₃.eval X

    set z₀ := z₀.eval X
    set z₁ := z₁.eval X
    set z₂ := z₂.eval X
    set z₃ := z₃.eval X

    set c₀ := c₀.eval X
    set c₁ := c₁.eval X
    set c₂ := c₂.eval X
    set c₃ := c₃.eval X

    constructor
    . intro h
      rcases h with ⟨hxyz0, hxyz1, hxyz2, hxyz3, hc0, hc1, hc2, hc3⟩

      have hz0 : z₀ = x₀ + y₀ - c₀ * 2 ^ 8 := by
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_right_comm, sub_eq_zero, eq_comm] at hxyz0
        exact hxyz0

      have hz1 : z₁ = x₁ + y₁ + c₀ - c₁ * 2 ^ 8 := by
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_right_comm, sub_eq_zero, eq_comm] at hxyz1
        exact hxyz1

      have hz2 : z₂ = x₂ + y₂ + c₁ - c₂ * 2 ^ 8 := by
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_right_comm, sub_eq_zero, eq_comm] at hxyz2
        exact hxyz2

      have hz3 : z₃ = x₃ + y₃ + c₂ - c₃ * 2 ^ 8 := by
        rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_right_comm, sub_eq_zero, eq_comm] at hxyz3
        exact hxyz3

      have hzexpr : (z₀ + z₁ * 2 ^ 8 + z₂ * 2 ^ 16 + z₃ * 2 ^ 24).val
        = (((x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃ * 2 ^ 24) +
          (y₀ + y₁ * 2 ^ 8 + y₂ * 2 ^ 16 + y₃ * 2 ^ 24)) - c₃ * 2 ^ 32).val := by
        rw [hz0, hz1, hz2, hz3]
        ring

      rw [hzexpr, sub_eq_add_neg, ZMod.val_add, ← neg_mul, ZMod.val_mul]
      simp
      -- soundness
      rcases hc3 with hzc3 | hoc3
      . apply And.intro
        rw [hzc3]
        simp
        rw [ZMod.val_add]
        simp
        sorry

      sorry

    . sorry

end Addition32
