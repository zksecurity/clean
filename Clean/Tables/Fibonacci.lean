import Clean.Utils.Field
import Clean.Expression
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasLehmer
import Clean.Gadgets.Addition8
import Clean.Gadgets.Equality
import Clean.Table

section FibonacciTable
open Expression
variable (p : ℕ) [Fact p.Prime] [Fact (p > 512)]
variable (M : ℕ) [M_large_enough: Fact (M ≥ 2)]

/-
Table layout:


fib_i    | fib_succ | carry
0        | 1        | c_0
1        | 1        | c_1
...
fib(i)   | fib(i+1) | c_i
fib(i+1) | fib(i+2) | c_i+1
-/

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n+2) => (fib8 n + fib8 (n+1)) % 256

def fib_i {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 0))
def fib_succ {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 1))
def carry {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 2))

def fibonacciTable : Table 3 M p := {
  constraints := [
    TableConstraint.boundary 0 (λ row => Equality.circuit 3 M (fib_i row) (const 0)),
    TableConstraint.boundary 0 (λ row => Equality.circuit 3 M (fib_succ row) (const 1)),
    TableConstraint.everyRowTwoRows M_large_enough (λ curr => λ next =>
      Addition8.circuit 3 M (fib_i curr) (fib_succ curr) (fib_succ next) (carry curr)
    ),
    TableConstraint.everyRowTwoRows M_large_enough (λ curr => λ next =>
      Equality.circuit 3 M (fib_succ curr) (fib_i next)
    )
  ],

  lookups := [
    -- the lookup is performed only on the second column, by induction we can show
    -- that the first column is a byte as well for all rows
    TableLookup.everyRow (λ row => ByteLookup.lookup 3 M (fib_succ row)),
  ],


  spec := fun trace => forAllRowsOfTraceWithIndex 3 M p trace
    (λ row index => (trace.eval (fib_i row)).val = fib8 index ∧
      (trace.eval (fib_i row)).val = fib8 (index + 1)),

  equiv := (by
    intros trace
    simp [TraceOfLength.eval, ByteLookup.lookup, Addition8.circuit, Equality.circuit, applyBoundary]
    simp [applyEveryRowSingleRow, applyEveryRowTwoRows, lookupEveryRow, forAllRowsOfTraceWithIndex, forallList]
    set trace' := trace.val
    induction trace' with
    | empty => {
      simp [lookupEveryRow.inner, forAllRowsOfTraceWithIndex.inner]
    }
    | cons rest' first_row ih => {
      induction rest' with
      | empty => {
        simp [lookupEveryRow.inner, forAllRowsOfTraceWithIndex.inner, Trace.len, fib8]
        simp [TraceOfLength.eval]
        intros byte_succ
        intros boundary
        constructor
        · sorry
        · sorry
      }
      | cons rest row ih => {
        sorry
      }
    }
  )
}


end FibonacciTable
