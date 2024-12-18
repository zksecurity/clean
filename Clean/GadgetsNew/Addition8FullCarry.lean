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

namespace Add8FullCarry
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

structure add8_full_inputs_struct (F : Type) where
  x: F
  y: F
  carry_in: F

-- TODO: the following should be derived automatically
-- ideally we would say
-- derive_provable_type add8_full_inputs_struct as add8_full_inputs with (Expression (F p)) (F p)
def add8_full_inputs (p : ℕ) : TypePair := ⟨
  add8_full_inputs_struct (Expression (F p)),
  add8_full_inputs_struct (F p)
⟩

instance : ProvableType (F p) (add8_full_inputs p) where
  size := 3
  to_vars s := vec [s.x, s.y, s.carry_in]
  from_vars v := ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩ ⟩
  to_values s := vec [s.x, s.y, s.carry_in]
  from_values v := ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩, v.get ⟨ 2, by norm_num ⟩ ⟩


structure add8_full_outputs_struct (F : Type) where
  z: F
  carry_out: F

def add8_full_outputs (p : ℕ) : TypePair := ⟨
  add8_full_outputs_struct (Expression (F p)),
  add8_full_outputs_struct (F p)
⟩

instance : ProvableType (F p) (add8_full_outputs p) where
  size := 2
  to_vars s := vec [s.z, s.carry_out]
  from_vars v := ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩ ⟩
  to_values s := vec [s.z, s.carry_out]
  from_values v := ⟨ v.get ⟨ 0, by norm_num ⟩, v.get ⟨ 1, by norm_num ⟩ ⟩


def add8_full_carry (input : (add8_full_inputs p).var) : Stateful (F p) (add8_full_outputs p).var := do
  let ⟨x, y, carry_in⟩ := input

  let z ← witness (fun () => mod_256 (x + y + carry_in))
  byte_lookup z

  let carry_out ← witness (fun () => floordiv (x + y + carry_in) 256)
  assert_bool carry_out

  assert_zero (x + y + carry_in - z - carry_out * (const 256))
  return {
    z := z,
    carry_out := carry_out
  }

def assumptions (input : (add8_full_inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (add8_full_inputs p).value) (out : (add8_full_outputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  out.z.val = (x.val + y.val + carry_in.val) % 256 ∧
  out.carry_out.val = (x.val + y.val + carry_in.val) / 256

def circuit : FormalCircuit (F p) (add8_full_inputs p) (add8_full_outputs p) where
  main := add8_full_carry
  assumptions := assumptions
  spec := spec
  soundness := by
    sorry
  completeness := by
    sorry
end Add8FullCarry
