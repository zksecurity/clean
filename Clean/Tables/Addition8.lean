import Clean.Utils.Field
import Clean.Expression
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8
import Clean.Table

/-
  Simple addition table: every row in the table must be a valid addition modulo 2^8
-/
section AdditionTable
open Expression
variable (T : ℕ+) (p : ℕ) [Fact p.Prime] [Fact (p > 512)]

def addConstraint : TableConstraint 4 T p := TableConstraint.everyRow
  (λ row => Addition8.circuit 4 T (var row 0) (var row 1) (var row 2) (var row 3))

def constraints : List (TableConstraint 4 T p) := [addConstraint T p]

def spec : Inputs 4 T (F p) -> Prop :=
  fun trace => (∀ row : ZMod T,
    (trace row 2).val = ((trace row 0).val + (trace row 1).val) % 256
    ∧ (trace row 3).val = ((trace row 0).val + (trace row 1).val) / 256)

def additionTable : Table 4 T p := {
  constraints := constraints T p,
  spec := spec T p,
  equiv := (by
    intros trace
    simp [forallList, fullLookupSet, fullConstraintSet, addConstraint, spec, eval, ByteLookup.lookup, Addition8.circuit]
    intro lookups
    constructor
    · intro h
      intro row
      have h := h row
      have lookups := lookups row
      have thm := Addition8.equiv 4 T (trace row 0) (trace row 1) (trace row 2) (trace row 3) trace
      simp [forallList, fullLookupSet, fullConstraintSet, ByteLookup.lookup, eval, Addition8.spec] at thm
      have thm_specialized := thm lookups.left lookups.right.left lookups.right.right
      rw [thm_specialized] at h
      assumption
    · intro h
      intro row
      have h := h row
      have lookups := lookups row
      have thm := Addition8.equiv 4 T (trace row 0) (trace row 1) (trace row 2) (trace row 3) trace
      simp [forallList, fullLookupSet, fullConstraintSet, ByteLookup.lookup, eval, Addition8.spec] at thm
      have thm_specialized := thm lookups.left lookups.right.left lookups.right.right
      rw [←thm_specialized] at h
      assumption
  )
}

end AdditionTable
