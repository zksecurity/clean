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

namespace Add8Full
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

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

  let res ← subcircuit Add8FullCarry.circuit {
    x := x,
    y := y,
    carry_in := carry_in
  }

  return res.z

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
    rintro ctx env inputs inputs_var h_inputs as
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    intro h_holds z

    -- characterize inputs
    have hx : x_var.eval_env env = x := by injection h_inputs
    have hy : y_var.eval_env env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval_env env = carry_in := by injection h_inputs

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Add8Full.circuit`
    dsimp at h_holds

    -- rewrite input and ouput values
    rw [hx, hy, hcarry_in] at h_holds
    rw [←(by rfl : z = env ctx.offset)] at h_holds

    -- satisfy `Add8Full.assumptions` by using our own assumptions
    let ⟨ asx, asy, as_carry_in ⟩ := as
    have as': Add8FullCarry.circuit.assumptions { x := x, y := y, carry_in := carry_in } := ⟨asx, asy, as_carry_in⟩
    specialize h_holds (by assumption)
    dsimp [ProvableType.from_values] at h_holds

    guard_hyp h_holds : Add8FullCarry.circuit.spec
      { x := x, y := y, carry_in := carry_in }
      { z := z, carry_out := env (ctx.offset + 1) }

    -- unfold `Add8Full` statements to show what the hypothesis is in our context
    dsimp [Add8FullCarry.circuit, Add8FullCarry.spec] at h_holds
    -- discard second part of the spec
    have ⟨ h_holds, _ ⟩ := h_holds
    guard_hyp h_holds : z.val = (x.val + y.val + carry_in.val) % 256
    exact h_holds

  completeness := by
    -- introductions
    rintro ctx inputs inputs_var h_inputs
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval = x := by injection h_inputs
    have hy : y_var.eval = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval = carry_in := by injection h_inputs

    -- simplify assumptions and goal
    dsimp [assumptions] at as
    dsimp
    rw [hx, hy, hcarry_in]

    -- the goal is just the `subcircuit_completeness` of `Add8Full.circuit`, i.e. the assumptions must hold
    -- simplify `Add8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Add8FullCarry.circuit, Add8FullCarry.assumptions]
    have ⟨ asx, asy, as_cin ⟩ := as
    simp [asx, asy, as_cin]

end Add8Full
