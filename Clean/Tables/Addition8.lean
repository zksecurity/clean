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
variable (M : ℕ) (p : ℕ) [Fact p.Prime] [Fact (p > 512)]

def additionTable : Table 4 M p := {
  constraints := [
     TableConstraint.everyRowSingleRow
      (λ row => Addition8.circuit 4 M (const (row 0)) (const (row 1)) (const (row 2)) (const (row 3)))
  ],

  lookups := [
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 M (const (row 0))),
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 M (const (row 1))),
    TableLookup.everyRow (λ row => ByteLookup.lookup 4 M (const (row 2))),
  ],


  spec := fun trace => forAllRowsOfTrace 4 M p trace (λ row =>
    let x := (trace.eval (const (row 0))).val
    let y := (trace.eval (const (row 1))).val
    let out := (trace.eval (const (row 2))).val
    let carry := (trace.eval (const (row 3))).val
    out = (x + y) % 256 ∧ carry = (x + y) / 256),

  equiv := (by
    intros trace
    simp [TraceOfLength.eval, ByteLookup.lookup, Addition8.circuit]
    simp [applyEveryRowSingleRow, lookupEveryRow,lookupEveryRow.inner, forAllRowsOfTrace, forallList]
    set trace' := trace.val
    induction trace' with
    | empty => {
      simp [forAllRowsOfTrace.inner]
    }
    | cons rest row ih => {
      simp
      simp [forallList] at ih
      intros byte_x ih_byte_x byte_y ih_byte_y byte_out ih_byte_out
      have ih' := ih ih_byte_x ih_byte_y ih_byte_out
      simp [forAllRowsOfTrace.inner]
      simp [fullConstraintSet.foldl]
      rw [ih']
      have thm := Addition8.equiv 4 M (const (row 0)) (const (row 1)) (const (row 2)) (const (row 3)) trace
      simp [ByteLookup.lookup, TraceOfLength.eval, Addition8.spec] at thm
      have thm_specialized := thm byte_x byte_y byte_out

      constructor
      · intro h3
        constructor
        · simp [TraceOfLength.eval] at h3
          have thm_h := And.intro h3.left h3.right.left
          rw [thm_specialized] at thm_h
          assumption
        · exact h3.right.right
      · intro h3
        rw [← and_assoc]
        constructor
        · simp [TraceOfLength.eval]
          have thm_h := h3.left
          rw [←thm_specialized] at thm_h
          exact thm_h
        · exact h3.right
    }
  )
}

end AdditionTable
