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
import Clean.GadgetsNew.Addition8Full

namespace Add8
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Circuit
open Provable (field field2 fields)
open ByteLookup
open Expression

def add8 (input : Vector (Expression (F p)) 2) := do
  let ⟨ [x, y], _ ⟩ := input
  let z ← subcircuit Add8Full.circuit {
    x := x,
    y := y,
    carry_in := const 0
  }
  return z

def spec (input : Vector (F p) 2) (z: F p) :=
  let ⟨ [x, y], _ ⟩ := input
  z.val = (x.val + y.val) % 256

def assumptions (input : Vector (F p) 2) :=
  let ⟨ [x, y], _ ⟩ := input
  x.val < 256 ∧ y.val < 256

def circuit : FormalCircuit (F p) (fields (F p) 2) (field (F p)) where
  main := add8
  assumptions := assumptions
  spec := spec
  soundness := by
    -- introductions
    rintro ctx env ⟨ inputs, _ ⟩ ⟨ inputs_var, _ ⟩ h_inputs as
    let [x, y] := inputs
    let [x_var, y_var] := inputs_var
    intro h_holds z

    -- characterize inputs
    injection h_inputs with h_inputs
    injection h_inputs with hx h_inputs
    injection h_inputs with hy h_inputs
    dsimp at hx hy

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Add8Full.circuit`
    dsimp at h_holds

    -- rewrite input and ouput values
    rw [hx, hy] at h_holds
    rw [←(by rfl : z = env ctx.offset)] at h_holds

    -- satisfy `Add8Full.assumptions` by using our own assumptions
    let ⟨ asx, asy ⟩ := as
    have as': Add8Full.assumptions { x := x, y := y, carry_in := 0 } := ⟨asx, asy, by tauto⟩
    specialize h_holds as'
    dsimp [ProvableType.from_values] at h_holds

    guard_hyp h_holds : Add8Full.circuit.spec { x := x, y := y, carry_in := 0 } z

    -- unfold `Add8Full` statements to show what the hypothesis is in our context
    dsimp [Add8Full.circuit, Add8Full.spec] at h_holds
    guard_hyp h_holds : z.val = (x.val + y.val + (0 : F p).val) % 256

    simp at h_holds
    exact h_holds

  completeness := by
    -- introductions
    rintro ctx ⟨ inputs, _ ⟩ ⟨ inputs_var, _ ⟩ h_inputs
    let [x, y] := inputs
    let [x_var, y_var] := inputs_var
    rintro as

    -- characterize inputs
    injection h_inputs with h_inputs
    injection h_inputs with hx h_inputs
    injection h_inputs with hy h_inputs
    dsimp at hx hy

    -- simplify assumptions and goal
    dsimp [assumptions] at as
    dsimp
    rw [hx, hy]

    -- the goal is just the `subcircuit_completeness` of `Add8Full.circuit`, i.e. the assumptions must hold
    -- simplify `Add8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Add8Full.circuit, Add8Full.assumptions]
    show x.val < 256 ∧ y.val < 256 ∧ (0 = 0 ∨ 0 = 1)
    have ⟨ asx, asy ⟩ := as
    exact ⟨ asx, asy, by tauto ⟩

end Add8
