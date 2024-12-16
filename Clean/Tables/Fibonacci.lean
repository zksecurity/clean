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
import Clean.Utils.Tactics

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


lemma fib8_always_byte (n : ℕ) : fib8 n < 256 := by
  induction' n using Nat.twoStepInduction
  repeat {simp [fib8]}; apply Nat.mod_lt; simp


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


  spec := fun trace => (forAllRowsOfTraceWithIndex 3 M p trace
    (λ row index =>
      (trace.eval (A row)).val = fib8 index ∧
      (trace.eval (B row)).val = fib8 (index + 1))) ∧
    forAllRowsOfTraceExceptLast 3 M p trace (λ row =>
      (trace.eval (carry row)).val = ((trace.eval (A row)).val + (trace.eval (B row)).val) / 256),

  equiv := (by
    intros trace
    simp [TraceOfLength.eval, ByteLookup.lookup]
    simp [fullTableConstraintSet, lookupEveryRow, forAllRowsOfTraceWithIndex, forAllRowsOfTraceExceptLast, forallList]
    set trace' := trace.val

    induction' trace' using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    -- empty trace
    · simp [forAllRowsOfTraceWithIndex.inner,
        forAllRowsOfTraceExceptLast.inner,
        fullTableConstraintSet.foldl,
        fib8]

    -- trace with only one row
    · simp [forAllRowsOfTraceWithIndex.inner, forAllRowsOfTraceExceptLast.inner,
        fib8, TraceOfLength.eval, fullTableConstraintSet.foldl]
      intro _
      have thm := Equality.equiv 3 M (B first_row) 1 trace
      simp [ByteLookup.lookup, TraceOfLength.eval, Equality.spec] at thm
      intro _
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
      specialize_auto ih2
      simp [fullTableConstraintSet.foldl, fib8, TraceOfLength.eval]
      simp [forallList, fullConstraintSet, fullConstraintSet.foldl]

      simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl,
        fib8, TraceOfLength.eval] at ih2
      rw [ih2]
      simp [forAllRowsOfTraceWithIndex.inner, forAllRowsOfTraceExceptLast.inner]

      have eq_relation := Equality.equiv 3 M (B curr) (A next) trace
      simp [TraceOfLength.eval, Equality.spec] at eq_relation
      rw [eq_relation]

      constructor
      -- soundness direction
      · simp
        intros c1 c2 c3 fib_curr fib_next ih_rest carry_correct

        -- first of all, we show that since there is the Eq constraint, the byte lookup argument
        -- is applied also to the first column
        have lookup_first : ZMod.val (curr 0) < 256 := by
          have lookup_curr_first := lookup_curr
          rw [c3] at lookup_curr_first
          cases rest with
          | empty =>{
            -- empty, this is true by boundary
            simp [fullConstraintSet.foldl, forAllRowsOfTraceExceptLast.inner, forAllRowsOfTraceWithIndex.inner] at ih2
            have constraints := ih2.mpr (And.intro fib_curr fib_next)
            simp [TraceOfLength.eval] at constraints
            have boundary1 := constraints.left
            rw [boundary1]
            simp
          }
          | cons rest prev => {
            -- at least one row above, this is true by the inductive hypothesis
            -- and the Eq constraint
            simp [forAllRowsOfTraceWithIndex.inner, fullTableConstraintSet.foldl,
              fib8, TraceOfLength.eval] at ih2
            simp [forAllRowsOfTraceWithIndex.inner] at ih_rest
            have constraints := ih2.mpr
            simp [ih_rest, fib_curr, fib_next, fib8, carry_correct] at constraints

            have eq_with_prev := constraints.right.right.left
            have eq_relation := Equality.equiv 3 M (B prev) (A curr) trace
            simp [TraceOfLength.eval, Equality.spec] at eq_relation
            rw [eq_relation] at eq_with_prev
            rw [←eq_with_prev]

            simp at lookup_rest
            have lookup_prev := lookup_rest.left
            assumption
          }

        -- here we show the first part of the spec, which is ZMod.val (next 0) = fib8 (rest +> curr).len
        -- this is trivial because of the Eq constraint
        have spec1 : ZMod.val (next 0) = fib8 (rest +> curr).len := by
          rw [c3] at fib_next
          simp [Trace.len]
          assumption

        -- here we show the second part of the spec, which is ZMod.val (next 1) = fib8 (rest +> curr +> next).len
        -- the addition constraints imply an add8 between the trace elements
        -- also we show that the carry is correct
        have spec2 : ZMod.val (next 1) = fib8 (rest +> curr +> next).len
          ∧ ZMod.val (curr 2) = (ZMod.val (curr 0) + ZMod.val (curr 1)) / 256
          := by
          have add_relation := Addition8.equiv 3 M (A curr) (B curr) (B next) (carry curr) trace
          simp [ByteLookup.lookup, TraceOfLength.eval, Addition8.spec] at add_relation
          specialize_auto add_relation

          -- and now we reason about fib
          have add_input := And.intro c1 c2
          rw [add_relation] at add_input
          simp [add_input.right]
          have add_h := add_input.left
          simp [fib8]
          rw [fib_curr] at add_h
          rw [fib_next] at add_h
          assumption

        -- putting all together
        simp [spec1, spec2, fib8, ih_rest, carry_correct, fib_next, fib_curr]

      -- completeness
      · intro h
        have ⟨⟨⟨fib_next0, fib_next1⟩, ⟨⟨fib_curr0, fib_curr1⟩, fib_ih⟩⟩, ⟨carry_curr, carry_ih⟩⟩ := h
        simp [carry_ih, fib_ih, fib_curr0, fib_curr1]

        -- addition
        have lookup_first := fib8_always_byte rest.len
        rw [←fib_curr0] at lookup_first

        have add_relation := Addition8.equiv 3 M (A curr) (B curr) (B next) (carry curr) trace
        simp [ByteLookup.lookup, TraceOfLength.eval, Addition8.spec] at add_relation
        specialize_auto add_relation

        nth_rewrite 1 [fib_curr0] at add_relation
        nth_rewrite 1 [fib_curr1] at add_relation
        nth_rewrite 1 [fib_next1] at add_relation
        simp [fib8, carry_curr] at add_relation
        simp [add_relation]

        -- Equality
        have h := fib_next0
        simp [Trace.len] at h
        rw [←fib_curr1] at h
        apply_fun ZMod.val
        · exact Eq.symm h
        · apply ZMod.val_injective
  )
}


end FibonacciTable
