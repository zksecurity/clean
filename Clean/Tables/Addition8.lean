import Clean.Utils.Field
import Clean.Expression
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8
import Clean.Table
import Clean.Gadgets.ByteLookup

/-
  Simple addition table: every row in the table must be a valid addition modulo 2^8
-/
section AdditionTable
open Expression
variable (T : ℕ+) (p : ℕ) [Fact p.Prime] [Fact (p > 512)]

def additionTable : Table 4 T p := {
  constraints := [
     TableConstraint.everyRow
      (λ row => Addition8.circuit 4 T (var row 0) (var row 1) (var row 2) (var row 3))
  ],

  lookups := [
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 T (var row 0)),
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 T (var row 1)),
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 T (var row 2)),
  ],

  spec := fun trace => (∀ row : ZMod T,
    (trace row 2).val = ((trace row 0).val + (trace row 1).val) % 256
    ∧ (trace row 3).val = ((trace row 0).val + (trace row 1).val) / 256),

  equiv := (by
    intros trace
    simp [eval, ByteLookup.lookup, Addition8.circuit]
    intro lookups
    constructor
    · intro h
      intro row
      have h := h row
      have lookups := lookups row
      have thm := Addition8.equiv 4 T (trace row 0) (trace row 1) (trace row 2) (trace row 3) trace
      simp [ByteLookup.lookup, eval, Addition8.spec] at thm
      have thm_specialized := thm lookups.left lookups.right.left lookups.right.right
      rw [thm_specialized] at h
      assumption
    · intro h
      intro row
      have h := h row
      have lookups := lookups row
      have thm := Addition8.equiv 4 T (trace row 0) (trace row 1) (trace row 2) (trace row 3) trace
      simp [ByteLookup.lookup, eval, Addition8.spec] at thm
      have thm_specialized := thm lookups.left lookups.right.left lookups.right.right
      rw [←thm_specialized] at h
      assumption
  )
}

end AdditionTable
