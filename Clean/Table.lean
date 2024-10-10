import Clean.Utils.Field
import Clean.Expression
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasLehmer
import Clean.Gadgets.Addition8

section Table
variable (N M : ℕ+) (p : ℕ) [Fact p.Prime]

/--
  A RowConstraint is a constraint that applies to a single row of a table.
  It is a function that takes the row index and returns a GenericConstraint.
-/
def RowConstraint := ZMod M -> GenericConstraint p N M

inductive TableConstraint where
  | boundary : ZMod M -> RowConstraint N M p -> TableConstraint
  | everyRow : RowConstraint N M p -> TableConstraint
  | everyRowExceptLast : RowConstraint N M p -> TableConstraint

structure Table where
  constraints : List (TableConstraint N M p)
  spec : Inputs N M (F p) -> ZMod M -> Prop
  equiv :
    ∀ trace : Inputs N M (F p), -- the inputs to the circuit
    ∀ row : ZMod M, -- row index
    forallList constraints (fun c => match c with
      | TableConstraint.boundary constraintRow c
        => forallList (fullLookupSet (c row)) (fun lookup => row = constraintRow -> lookup.prop trace)
      | TableConstraint.everyRow c
        => forallList (fullLookupSet (c row)) ((fun lookup => lookup.prop trace))
      | TableConstraint.everyRowExceptLast c
        => forallList (fullLookupSet (c row)) ((fun lookup => row.val < (M-1) -> lookup.prop trace))
    ) ->
    (
      forallList constraints (fun c => match c with
        | TableConstraint.boundary constraintRow c
          => forallList (fullConstraintSet (c row)) (fun constraint => row = constraintRow -> constraint.eval trace = 0)
        | TableConstraint.everyRow c
          => forallList (fullConstraintSet (c row)) ((fun constraint => constraint.eval trace = 0))
        | TableConstraint.everyRowExceptLast c
          => forallList (fullConstraintSet (c row)) ((fun constraint => row.val < (M-1) -> constraint.eval trace = 0)))
      ↔
      spec trace row
    )


end Table


section
open Expression
variable (T : ℕ+) (p : ℕ) [Fact p.Prime] [Fact (p > 512)]

-- Proof of Concept example: every row in the table must be a valid addition modulo 2^8
def addConstraint : TableConstraint 4 T p := TableConstraint.everyRow
  (λ row => Addition8.circuit 4 T (var row.val 0) (var row.val 1) (var row.val 2) (var row.val 3))

def constraints : List (TableConstraint 4 T p) := [addConstraint T p]

def spec : Inputs 4 T (F p) -> ZMod T -> Prop := fun env => fun i => (env i 2).val = ((env i 0).val + (env i 1).val) % 256 ∧ (env i 3).val = ((env i 0).val + (env i 1).val) / 256

def equiv : ∀ (trace : Inputs 4 T (F p)) (row : ZMod ↑T),
  (forallList (constraints T p) fun c ↦
      match c with
      | TableConstraint.boundary constraintRow c =>
        forallList (fullLookupSet (c row)) fun lookup ↦ row = constraintRow → lookup.prop trace
      | TableConstraint.everyRow c => forallList (fullLookupSet (c row)) fun lookup ↦ lookup.prop trace
      | TableConstraint.everyRowExceptLast c =>
        forallList (fullLookupSet (c row)) fun lookup ↦ row.val < ↑T - 1 → lookup.prop trace) →
    ((forallList (constraints T p) fun c ↦
        match c with
        | TableConstraint.boundary constraintRow c =>
          forallList (fullConstraintSet (c row)) fun constraint ↦ row = constraintRow → eval trace constraint = 0
        | TableConstraint.everyRow c =>
          forallList (fullConstraintSet (c row)) fun constraint ↦ eval trace constraint = 0
        | TableConstraint.everyRowExceptLast c =>
          forallList (fullConstraintSet (c row)) fun constraint ↦ row.val < ↑T - 1 → eval trace constraint = 0) ↔
      spec T p trace row)
  := by
  intros trace row
  simp [forallList, fullLookupSet, fullConstraintSet, addConstraint, spec, eval, ByteLookup.lookup, Addition8.circuit]
  let x : Expression 4 T (F p) := var row 0
  let y : Expression 4 T (F p) := var row 1
  let out : Expression 4 T (F p) := var row 2
  let carry : Expression 4 T (F p) := var row 3

  intros byte_x byte_y byte_out

  -- this is a very trivial case where the Add8 spec is applied every row,
  -- so we can just reuse the equivalenve theorem from Addition8
  have thm := Addition8.equiv 4 T x y out carry trace
  simp [forallList, fullLookupSet, fullConstraintSet, ByteLookup.lookup, eval, Addition8.spec] at thm
  have thm_specialized := thm byte_x byte_y byte_out


  assumption


def additionTable : Table 4 T p := {
  constraints := constraints T p,
  spec := spec T p,
  equiv := equiv T p
}

end
