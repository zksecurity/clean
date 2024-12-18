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

namespace Add8Full
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

def add8_full (input : (add8_full_inputs p).var) := do
  let ⟨x, y, carry_in⟩ := input

  let z ← witness (fun () => mod_256 (x + y + carry_in))
  byte_lookup z

  let carry_out ← witness (fun () => floordiv (x + y + carry_in) 256)
  assert_bool carry_out

  assert_zero (x + y + carry_in - z - carry_out * (const 256))
  return z

def assumptions (input : (add8_full_inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (add8_full_inputs p).value) (z: F p) :=
  let ⟨x, y, carry_in⟩ := input
  z.val = (x.val + y.val + carry_in.val) % 256

def circuit : FormalCircuit (F p) (add8_full_inputs p) (field (F p)) where
  main := add8_full
  assumptions := assumptions
  spec := spec
  soundness := by
    -- introductions
    rintro env inputs inputs_var h_inputs as
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro h_holds z'

    -- characterize inputs
    have hx : x_var.eval_env env = x := by injection h_inputs
    have hy : y_var.eval_env env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval_env env = carry_in := by injection h_inputs

    -- simplify constraints hypothesis
    dsimp at h_holds
    let z := env 0
    let carry_out := env 1
    rw [←(by rfl : z = env 0), ←(by rfl : carry_out = env 1)] at h_holds
    rw [hx, hy, hcarry_in] at h_holds
    let ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    -- characterize output and replace in spec
    rw [(by rfl : z' = z)]

    -- simplify assumptions and spec
    dsimp [spec]
    dsimp [assumptions] at as

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)
    guard_hyp h_byte: ByteTable.contains (vec [z])
    guard_hyp h_bool_carry: carry_out * (carry_out + -1 * 1) = 0
    guard_hyp h_add: x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0

    show z.val = (x.val + y.val + carry_in.val) % 256

    -- reuse Boolean.equiv
    have h_bool_carry': carry_out = 0 ∨ carry_out = 1 := (Boolean.equiv carry_out).mp h_bool_carry
    -- reuse ByteTable.soundness
    have h_byte': z.val < 256 := ByteTable.soundness z h_byte
    sorry


  completeness := by
    -- introductions
    rintro inputs inputs_var h_inputs
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval = x := by injection h_inputs
    have hy : y_var.eval = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval = carry_in := by injection h_inputs

    -- simplify assumptions
    dsimp [assumptions] at as

    -- unfold goal, (re)introduce names for some of unfolded variables
    dsimp
    rw [hx, hy, hcarry_in]
    let z := mod_256 (x + y + carry_in)
    let carry_out := floordiv (x + y + carry_in) 256
    rw [←(by rfl : z = mod_256 (x + y + carry_in))]
    rw [←(by rfl : carry_out = floordiv (x + y + carry_in) 256)]

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

    let goal_byte := ByteTable.contains (vec [z])
    let goal_bool := carry_out * (carry_out + -1 * 1) = 0
    let goal_add := x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add
    sorry
end Add8Full
