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
Fibonacci table layout:


A        | B        | carry
--------------------------------
0        | 1        | c_0
1        | 1        | c_1
...
fib(i)   | fib(i+1) | c_i
fib(i+1) | fib(i+2) | c_i+1
...

-/

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n+2) => (fib8 n + fib8 (n+1)) % 256

def A {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 0))
def B {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 1))
def carry {p M : ℕ} (row : Row 3 (F p)) : Expression 3 M (F p) := (const (row 2))

def fibonacciTable : Table 3 M p := {
  constraints := [
    TableConstraint.boundary 0 (λ row => Equality.circuit 3 M (A row) 0),
    TableConstraint.boundary 0 (λ row => Equality.circuit 3 M (B row) 1),
    TableConstraint.everyRowTwoRows M_large_enough (λ curr => λ next =>
      Addition8.circuit 3 M (A curr) (B curr) (B next) (carry curr)
    ),
    TableConstraint.everyRowTwoRows M_large_enough (λ curr => λ next =>
      Equality.circuit 3 M (B curr) (A next)
    )
  ],

  lookups := [
    -- the lookup is performed only on the second column, by induction we can show
    -- that the first column is a byte as well for all rows
    TableLookup.everyRow (λ row => ByteLookup.lookup 3 M (B row)),
  ],


  spec := fun trace => forAllRowsOfTraceWithIndex 3 M p trace
    (λ row index => (trace.eval (A row)).val = fib8 index ∧
      (trace.eval (B row)).val = fib8 (index + 1)),

  equiv := (by
    intros trace
    simp [TraceOfLength.eval, ByteLookup.lookup]
    simp [fullTableConstraintSet, lookupEveryRow, forAllRowsOfTraceWithIndex, forallList]
    set trace' := trace.val

    induction' trace' using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    -- empty trace
    · simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl, fib8]

    -- trace with only one row
    · simp [forAllRowsOfTraceWithIndex.inner, fib8, TraceOfLength.eval, fullTableConstraintSet.foldl]
      intro _
      have thm := Equality.equiv 3 M (B first_row) 1 trace
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
    -- we only need ih2 which is the induction hypothesis for two rows above (i.e., for rest)
    · simp
      simp at ih2
      intro lookup_next lookup_curr lookup_rest
      specialize ih2 lookup_curr lookup_rest
      simp [fullTableConstraintSet.foldl, fib8, TraceOfLength.eval]
      simp [forallList, fullConstraintSet, fullConstraintSet.foldl]

      simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl,
        fib8, TraceOfLength.eval] at ih2
      rw [ih2]
      simp [forAllRowsOfTraceWithIndex.inner]

      have eq_relation := Equality.equiv 3 M (B curr) (A next) trace
      simp [TraceOfLength.eval, Equality.spec] at eq_relation
      rw [eq_relation]

      constructor
      -- soundness direction
      · simp
        intros c1 c2 c3 fib_curr fib_next ih_rest
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
              cases rest with
              | empty =>{
                -- empty, this is true by boundary
                simp at ih2
                have constraints := ih2.mpr (And.intro (And.intro fib_curr fib_next) ih_rest)
                simp [TraceOfLength.eval] at constraints
                have boundary1 := constraints.left
                rw [boundary1]
                simp
              }
              | cons rest prev => {
                -- at least one row below, this is true by the inductive hypothesis
                -- and the Eq constraint
                simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl, fib8, TraceOfLength.eval] at ih2
                have constraints := ih2.mpr (And.intro (And.intro fib_curr fib_next) ih_rest)
                simp [TraceOfLength.eval] at constraints

                have eq_with_prev := constraints.right.right.left
                have eq_relation := Equality.equiv 3 M (B prev) (A curr) trace
                simp [TraceOfLength.eval, Equality.spec] at eq_relation
                rw [eq_relation] at eq_with_prev
                rw [←eq_with_prev]

                simp at lookup_rest
                have lookup_prev := lookup_rest.left
                assumption
              }

            -- the addition constraints imply an add8 between the trace elements
            have add_relation := Addition8.equiv 3 M (A curr) (B curr) (B next) (carry curr) trace
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
