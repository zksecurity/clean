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
variable (p : ℕ) [Fact p.Prime] [p_large_enough: Fact (p > 512)]
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
      (trace.eval (fib_succ row)).val = fib8 (index + 1)),

  equiv := (by
    intros trace
    simp [TraceOfLength.eval, ByteLookup.lookup]
    simp [fullTableConstraintSet, lookupEveryRow, forAllRowsOfTraceWithIndex, forallList]
    set trace' := trace.val

    induction' trace' using Trace.everyRowTwoRowsInduction with first_row curr next rest ih1 ih2
    -- empty trace
    · simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl, fib8]

    -- trace with only one row
    · simp [forAllRowsOfTraceWithIndex.inner, fib8, TraceOfLength.eval, fullTableConstraintSet.foldl]
      intro _
      have thm := Equality.equiv 3 M (const (first_row 1)) (const 1) trace
      simp [ByteLookup.lookup, TraceOfLength.eval, Equality.spec] at thm
      intro h
      rw [thm]

      have val_one_is_one := FieldUtils.val_lt_p 1 (Nat.lt_trans (by norm_num) p_large_enough.elim)
      simp at val_one_is_one
      rw [←val_one_is_one]
      constructor
      · intro h; rw [h];
      · intro h; apply_fun ZMod.val; rw [h]; apply ZMod.val_injective

    -- inductive case: trace with at least two rows
    -- ih1 is the induction hypothesis for the previous row, and
    -- ih2 is the induction hypothesis for two rows above
    · simp
      simp at ih1
      simp at ih2
      intro lookup_next lookup_curr lookup_rest
      have ih1 := ih1 lookup_rest
      have ih2 := ih2 lookup_curr lookup_rest
      simp [fib8, TraceOfLength.eval, forallList, fullTableConstraintSet.foldl, fullConstraintSet.foldl]
      simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl, fib8, TraceOfLength.eval] at ih1
      simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl, fib8, TraceOfLength.eval] at ih2
      --the following is a very nice rewrite of the inductive hypothesis
      rw [ih2]
      simp [forAllRowsOfTraceWithIndex.inner]

      constructor
      -- soundness direction
      · simp
        intros c1 c2 c3 fib_curr fib_next ih_rest
        have eq_relation := Equality.equiv 3 M (const (curr 1)) (const (next 0)) trace
        simp [TraceOfLength.eval, Equality.spec] at eq_relation
        rw [eq_relation] at c3

        constructor
        · constructor
          · -- here we need to prove the first part of the spec, which is ZMod.val (next 0) = fib8 (rest +> curr).len
            -- this is trivial because of the Eq constraint
            rw [c3] at fib_next
            simp [Trace.len]
            assumption
          · -- here we need to prove the second part of the spec, which is ZMod.val (next 1) = fib8 (rest +> curr +> next).len

            -- first of all, we show that since there is the Eq constraint, the byte lookup argument
            -- is applied also to the first column
            have lookup_first : ZMod.val (curr 0) < 256 := by
              have lookup_curr_first := lookup_curr
              rw [c3] at lookup_curr_first
              -- TODO: somehow, but should be doable :)
              sorry

            -- the addition constraints imply an add8 between the trace elements
            have add_relation := Addition8.equiv 3 M (const (curr 0)) (const (curr 1)) (const (next 1)) (const (curr 2)) trace
            simp [ByteLookup.lookup, TraceOfLength.eval, Addition8.spec] at add_relation
            have add_relation := add_relation lookup_first lookup_curr lookup_next

            have add_input := And.intro c1 c2
            rw [add_relation] at add_input
            have add_h := add_input.left

            -- and now we reason about fib
            simp [fib8]
            rw [fib_curr] at add_h
            rw [fib_next] at add_h
            assumption
        · constructor; constructor
          repeat {assumption}

      -- TODO: completeness
      · sorry
  )
}


end FibonacciTable
