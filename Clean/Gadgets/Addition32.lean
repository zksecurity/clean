import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8
import Clean.Gadgets.Xor

namespace Addition32
open Expression

variable {p : ℕ} [p_is_prime: Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- Addition of elements from GL(2 ^ 32) as
-- x = x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃ * 2 ^ 24 : ∀ i xi < 2 ^ 8


def lookup (N M : ℕ+) (x : Expression (F p)) (n : ℕ+) : LookupArgument p N M :=
  {
    prop := fun env => (x.eval env).val < n
  }

def AdditionConstraint (N M : ℕ+)
  (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ s₁ s₂ s₃ cs₁ cs₂ cs₃ : Expression (F p))
: GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x₀ + y₀ - z₀ - c₀ * const (256),
      s₁ + c₀ - z₁ - c₁ * const (256),
      x₂ + y₂ + c₁ - z₂ - c₂ * const (256),
      x₃ + y₃ + c₂ - z₃ - c₃ * const (256)
    ]

    [
      lookup N M x₀ 256, lookup N M x₁ 256, lookup N M x₂ 256, lookup N M x₃ 256,
      lookup N M y₀ 256, lookup N M y₁ 256, lookup N M y₂ 256, lookup N M y₃ 256,
      lookup N M z₀ 256, lookup N M z₁ 256, lookup N M z₂ 256, lookup N M z₃ 256,
    ]

    [
      Addition8.circuit N M x₁ y₁ s₁ cs₁,
      Addition8.circuit N M x₂ y₂ s₂ cs₂,
      Addition8.circuit N M x₁ y₁ s₁ cs₁,
      Xor.circuit N M c₁ c₀ cs₁,
      Xor.circuit N M c₂ c₁ cs₂,
      Xor.circuit N M c₃ c₂ cs₂,
      Boolean.circuit N M c₀,
      Boolean.circuit N M c₁,
      Boolean.circuit N M c₂,
      Boolean.circuit N M c₃
    ]

def spec (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
  : Inputs N M (F p) -> Prop :=
    (fun env =>
      have x := (x₀.eval env).val + (x₁.eval env).val * 2 ^ 8 +
                (x₂.eval env).val * 2 ^ 16 + (x₃.eval env).val * 2 ^ 24;

      have y := (y₀.eval env).val + (y₁.eval env).val * 2 ^ 8 +
                (y₂.eval env).val * 2 ^ 16 + (y₃.eval env).val * 2 ^ 24;

      have z := (z₀.eval env).val + (z₁.eval env).val * 2 ^ 8 +
                (z₂.eval env).val * 2 ^ 16 + (z₃.eval env).val * 2 ^ 24;

      have c₃ := (c₃.eval env).val;

      z = (x + y) % 2 ^ 32 ∧ c₃  = (x + y) / 2 ^ 32
    )


theorem half_adder8 (N M : ℕ+) (x y z c_out  : F p) (X :  Inputs N M (F p))
  (x_byte : x.val < 256) (y_byte : y.val < 256) (z_byte : z.val < 256) :
  x + y + -z + -(c_out * 256) = 0 ∧ (c_out = 0 ∨ c_out = 1) ↔
  z.val = (x.val + y.val) % 256 ∧ c_out.val = (x.val + y.val) / 256 := by sorry


theorem adder8 (N M : ℕ+) (x y z c_in c_out s cs  : F p) (X :  Inputs N M (F p))
  (x_byte : x.val < 256) (y_byte : y.val < 256) (z_byte : z.val < 256) (s_byte : s.val < 256) :
  c_in = 0 ∨ c_in = 1 -> (x + y + c_in + -z + -(c_out * 256) = 0 ∧ (c_out = 0 ∨ c_out = 1)
  ↔
  z.val = (x.val + y.val + c_in.val) % 256 ∧ c_out.val = (x.val + y.val + c_in.val) / 256) := by

  intro hc_in
  have add8_xy := Addition8.equiv N M x y s cs X
  have add8_sz := Addition8.equiv N M s c_in z c_out X
  simp [forallList, Boolean.spec, ByteLookup.lookup ] at add8_xy add8_sz
  rw [Addition8.spec] at add8_xy add8_sz
  simp [eval] at add8_xy add8_sz

  have c_in_byte : c_in.val < 256 := by
    rcases hc_in with hc_in_zero | hc_in_one
    { rw [hc_in_zero]; simp }
    { rw [hc_in_one, ZMod.val_one]; simp }

  constructor
  . intro h
    rcases h with ⟨hxy, hc_out⟩
    have : z = x + y + c_in - (c_out * 256) := by
       rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_right_comm, sub_eq_zero, eq_comm] at hxy
       exact hxy
    rw [this]
    sorry
  . sorry




-- theorem equiv (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p)) :
--   (∀ X,
--     (forallList
--          (fullLookupSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
--          (fun lookup => lookup.prop X))
--     -> (
--       (forallList
--          (fullConstraintSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
--          (fun constraint => constraint.eval X = 0))
--       ↔
--       spec N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ X
--     )
--   ) := by

--     intro X

--     simp [forallList, ByteLookup.lookup]

--     intro hx0_byte hx1_byte hx2_byte hx3_byte
--           hy0_byte hy1_byte hy2_byte hy3_byte
--           hz0_byte hz1_byte hz2_byte hz3_byte

--     simp [lookup] at hx0_byte hx1_byte hx2_byte hx3_byte
--                      hy0_byte hy1_byte hy2_byte hy3_byte
--                      hz0_byte hz1_byte hz2_byte hz3_byte

--     let equivBoolean0 := Boolean.equiv N M c₀ X
--     let equivBoolean1 := Boolean.equiv N M c₁ X
--     let equivBoolean2 := Boolean.equiv N M c₂ X
--     let equivBoolean3 := Boolean.equiv N M c₃ X
--     simp [forallList, Boolean.spec] at equivBoolean0
--     simp [forallList, Boolean.spec] at equivBoolean1
--     simp [forallList, Boolean.spec] at equivBoolean2
--     simp [forallList, Boolean.spec] at equivBoolean3
--     rw [equivBoolean0, equivBoolean1, equivBoolean2, equivBoolean3, spec]

--     simp [spec, eval]

--     set x₀ := x₀.eval X
--     set x₁ := x₁.eval X
--     set x₂ := x₂.eval X
--     set x₃ := x₃.eval X

--     set y₀ := y₀.eval X
--     set y₁ := y₁.eval X
--     set y₂ := y₂.eval X
--     set y₃ := y₃.eval X

--     set z₀ := z₀.eval X
--     set z₁ := z₁.eval X
--     set z₂ := z₂.eval X
--     set z₃ := z₃.eval X

--     set c₀ := c₀.eval X
--     set c₁ := c₁.eval X
--     set c₂ := c₂.eval X
--     set c₃ := c₃.eval X



-- end Addition32
