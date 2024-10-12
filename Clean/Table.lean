import Clean.Utils.Field
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section Table
variable (N M : ℕ+) (p : ℕ) [Fact p.Prime]

/--
  A RowConstraint is a constraint that applies to a single row of a table.
  It is a function that takes the row index and returns a GenericConstraint.
-/
def RowConstraint := ZMod M -> GenericConstraint p N M

/--
  A TableConstraint is a constraint that applies to a table.
  It is either
  - a boundary constraint, which applies to one specific row of the table,
  - an everyRow constraint, which applies to every row of the table,
  - an everyRowExceptLast constraint, which applies to every row except the last one.
-/
inductive TableConstraint where
  | boundary : ZMod M -> RowConstraint N M p -> TableConstraint
  | everyRow : RowConstraint N M p -> TableConstraint
  | everyRowExceptLast : RowConstraint N M p -> TableConstraint

def RowLookup := ZMod M -> LookupArgument p N M

inductive TableLookup where
  | everyRow : RowLookup N M p -> TableLookup

/--
  A Table is a structure that represents a table of size N x M.
  It contains a list of constraints that apply to the table,
  and a specification.

  The equivalence theorem states the following:
  for all traces, given that all lookups are satisfied,
  the spec is satisfied if and only if all constraints are satisfied.
-/
structure Table where
  constraints : List (TableConstraint N M p)
  lookups : List (TableLookup N M p)
  spec : Inputs N M (F p) -> Prop
  equiv :
    ∀ trace : Inputs N M (F p),
    (∀ row : ZMod M, forallList lookups (fun c => match c with
      | TableLookup.everyRow lookup => (lookup row).prop trace)
    ) ->
    (
      (∀ row : ZMod M, forallList constraints (fun c => match c with
        | TableConstraint.boundary constraintRow c
          => forallList (fullConstraintSet (c row)) (fun constraint => row = constraintRow -> constraint.eval trace = 0)
        | TableConstraint.everyRow c
          => forallList (fullConstraintSet (c row)) ((fun constraint => constraint.eval trace = 0))
        | TableConstraint.everyRowExceptLast c
          => forallList (fullConstraintSet (c row)) ((fun constraint => row.val < (M-1) -> constraint.eval trace = 0))))
      ↔
      spec trace
    )


end Table
