import Clean.Utils.Field
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Gadgets.Addition8

section Table
variable (N : ℕ+) (M : ℕ) (p : ℕ) [Fact p.Prime]


def forAllRowsOfTrace : InputsOfLength N (F p) M -> (Row N (F p) -> Prop) -> Prop :=
  fun trace prop => forAllRowsOfTraceAux trace.val prop
  where
  forAllRowsOfTraceAux : Inputs N (F p) -> (Row N (F p) -> Prop) -> Prop
    | Inputs.empty, _ => true
    | (Inputs.cons row rest), prop => prop row ∧ forAllRowsOfTraceAux rest prop


def TableConstraint := InputsOfLength N (F p) M -> List (Expression N M (F p))

def everyRowConstraint (c : Row N (F p) -> GenericConstraint p N M) : TableConstraint N M p :=
  fun trace => everyRowConstraintAux c trace.val
  where
  everyRowConstraintAux (c : Row N (F p) -> GenericConstraint p N M) : Inputs N (F p) -> List (Expression N M (F p))
  | Inputs.empty => []
  | (Inputs.cons row rest) => fullConstraintSet (c row) ++ everyRowConstraintAux c rest

def TableLookup := InputsOfLength N (F p) M -> List (LookupArgument p N M)

def everyRowLookup (c : Row N (F p) -> LookupArgument p N M) : TableLookup N M p :=
  fun trace => everyRowLookupAux c trace.val
  where
  everyRowLookupAux (c : Row N (F p) -> LookupArgument p N M) : Inputs N (F p) -> List (LookupArgument p N M)
  | Inputs.empty => []
  | (Inputs.cons row rest) => [(c row)] ++ everyRowLookupAux c rest

def RowLookup := ZMod M -> LookupArgument p N M


inductive TableLookupStructures where
  | everyRow : (Row N (F p) -> LookupArgument p N M) -> TableLookupStructures

inductive TableConstraintStructures where
  | everyRow : (Row N (F p) -> GenericConstraint p N M) -> TableConstraintStructures

/--
  A Table is a structure that represents a table of size N x M.
  It contains a list of constraints that apply to the table,
  and a specification.

  The equivalence theorem states the following:
  for all traces, given that all lookups are satisfied,
  the spec is satisfied if and only if all constraints are satisfied.
-/
structure Table where
  constraints : List (TableConstraintStructures N M p)
  lookups : List (TableLookupStructures N M p)
  spec : InputsOfLength N (F p) M -> Prop
  equiv :
    ∀ trace : InputsOfLength N (F p) M,
    (forallList lookups (fun c => match c with
      | TableLookupStructures.everyRow lookup =>
        forallList ((everyRowLookup N M p lookup) trace) (λ c => c.prop trace))
    )
    ->
    (
      (forallList constraints (fun c => match c with
        | TableConstraintStructures.everyRow c
          => forallList ((everyRowConstraint N M p c) trace) (fun constraint => trace.eval constraint = 0))
      )
      ↔
      spec trace
    )


-- quick and dirty PoC
open Expression

variable [Fact (p > 512)]
def additionTable : Table 4 M p := {
  constraints := [
     TableConstraintStructures.everyRow
      (λ row => Addition8.circuit 4 M (const (row 0)) (const (row 1)) (const (row 2)) (const (row 3)))
  ],

  lookups := [
    TableLookupStructures.everyRow (λ row => ByteLookup.lookup 4 M (const (row 0))),
    TableLookupStructures.everyRow (λ row => ByteLookup.lookup 4 M (const (row 1))),
    TableLookupStructures.everyRow (λ row => ByteLookup.lookup 4 M (const (row 2))),
  ],


  spec := fun trace => forAllRowsOfTrace 4 M p trace (λ row =>
    let x := (trace.eval (const (row 0))).val
    let y := (trace.eval (const (row 1))).val
    let out := (trace.eval (const (row 2))).val
    let carry := (trace.eval (const (row 3))).val
    out = (x + y) % 256 ∧ carry = (x + y) / 256),

  equiv := (by
    intros trace
    simp [InputsOfLength.eval, ByteLookup.lookup, Addition8.circuit]
    simp [everyRowConstraint, everyRowLookup,everyRowLookup.everyRowLookupAux, forAllRowsOfTrace, forallList]
    set trace' := trace.val
    induction trace' with
    | empty => {
      simp [forAllRowsOfTrace.forAllRowsOfTraceAux]
    }
    | cons row rest ih => {
      simp
      simp [forallList] at ih
      intros byte_x ih_byte_x byte_y ih_byte_y byte_out ih_byte_out
      have ih' := ih ih_byte_x ih_byte_y ih_byte_out
      simp [forAllRowsOfTrace.forAllRowsOfTraceAux]
      simp [fullConstraintSet.foldl]
      rw [ih']
      have thm := Addition8.equiv 4 M (const (row 0)) (const (row 1)) (const (row 2)) (const (row 3)) trace
      simp [ByteLookup.lookup, InputsOfLength.eval, Addition8.spec] at thm
      have thm_specialized := thm byte_x byte_y byte_out

      constructor
      · intro h3
        constructor
        · simp [InputsOfLength.eval] at h3
          have thm_h := And.intro h3.left h3.right.left
          rw [thm_specialized] at thm_h
          assumption
        · exact h3.right.right
      · intro h3
        rw [← and_assoc]
        constructor
        · simp [InputsOfLength.eval]
          have thm_h := h3.left
          rw [←thm_specialized] at thm_h
          exact thm_h
        · exact h3.right
    }
  )
}


end Table
