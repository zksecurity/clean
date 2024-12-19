import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.GadgetsNew.ByteLookup
import Clean.GadgetsNew.Boolean
import Clean.GadgetsNew.Addition8FullCarry
import Clean.Types.U32

namespace Addition32Full
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def less_than_p [p_pos: Fact (p ≠ 0)] (x: F p) : x.val < p := by
  rcases p
  · have : 0 ≠ 0 := p_pos.elim; tauto
  · exact x.is_lt

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  FieldUtils.nat_to_field (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod_256 (x: F p) : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv [Fact (p ≠ 0)] (x: F p) (c: ℕ+) : F p :=
  FieldUtils.nat_to_field (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])


open Circuit
open Provable (field field2 fields)
open ByteLookup
open Expression

structure add32_inputs_struct (F : Type) where
  x: U32 F
  y: U32 F
  carry_in: F

def add32_full_inputs (p : ℕ) : TypePair := ⟨
  add32_inputs_struct (Expression (F p)),
  add32_inputs_struct (F p)
⟩

-- TODO: we *really* need to derive this automatically
instance : ProvableType (F p) (add32_full_inputs p) where
  size := 9 -- 4 + 4 + 1
  to_vars s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.carry_in]
  from_vars v := ⟨
    ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩, v.get ⟨ 3, by norm_num ⟩ ⟩,
    ⟨ v.get ⟨ 4, by norm_num ⟩, v.get ⟨ 5, by norm_num ⟩, v.get ⟨ 6, by norm_num ⟩, v.get ⟨ 7, by norm_num ⟩ ⟩,
    v.get ⟨ 8, by norm_num ⟩
  ⟩
  to_values s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.carry_in]
  from_values v := ⟨
    ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩, v.get ⟨ 3, by norm_num ⟩ ⟩,
    ⟨ v.get ⟨ 4, by norm_num ⟩, v.get ⟨ 5, by norm_num ⟩, v.get ⟨ 6, by norm_num ⟩, v.get ⟨ 7, by norm_num ⟩ ⟩,
    v.get ⟨ 8, by norm_num ⟩
  ⟩


structure add32_output_struct (F : Type) where
  z: U32 F
  carry_out: F

def add32_full_output (p : ℕ) : TypePair := ⟨
  add32_output_struct (Expression (F p)),
  add32_output_struct (F p)
⟩

instance : ProvableType (F p) (add32_full_output p) where
  size := 5 -- 4 + 1
  to_vars s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.carry_out]
  from_vars v := ⟨
    ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩, v.get ⟨ 3, by norm_num ⟩ ⟩,
    v.get ⟨ 4, by norm_num ⟩
  ⟩
  to_values s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.carry_out]
  from_values v := ⟨
    ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩, v.get ⟨ 3, by norm_num ⟩ ⟩,
    v.get ⟨ 4, by norm_num ⟩
  ⟩

def add32_full (input : (add32_full_inputs p).var) : Stateful (F p) (add32_full_output p).var := do
  let ⟨x, y, carry_in⟩ := input

  let {
    z := z0,
    carry_out := c0
  } ← Add8FullCarry.add8_full_carry ⟨ x.x0, y.x0, carry_in ⟩

  let {
    z := z1,
    carry_out := c1
  } ← Add8FullCarry.add8_full_carry ⟨ x.x1, y.x1, c0 ⟩

  let {
    z := z2,
    carry_out := c2
  } ← Add8FullCarry.add8_full_carry ⟨ x.x2, y.x2, c1 ⟩

  let {
    z := z3,
    carry_out := c3
  } ← Add8FullCarry.add8_full_carry ⟨ x.x3, y.x3, c2 ⟩

  return {
    z := U32.mk z0 z1 z2 z3,
    carry_out := c3
  }

def assumptions (input : (add32_full_inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.is_normalized ∧ y.is_normalized ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (add32_full_inputs p).value) (out: (add32_full_output p).value) :=
  let ⟨x, y, carry_in⟩ := input
  let ⟨z, carry_out⟩ := out
  z.value = (x.value + y.value + carry_in.val) % 2^32 ∧
  z.is_normalized ∧
  carry_out.val = (x.value + y.value + carry_in.val) / 2^32

def circuit : FormalCircuit (F p) (add32_full_inputs p) (add32_full_output p) where
  main := add32_full
  assumptions := assumptions
  spec := spec
  soundness := by
    sorry

  completeness := by
    sorry
end Addition32Full