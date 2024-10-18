import Clean.Utils.Field
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section Table
variable (N : ℕ+) (M : ℕ) (p : ℕ) [Fact p.Prime]

/--
  Apply a proposition to every row in the trace
-/
def forAllRowsOfTrace (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
def forAllRowsOfTraceWithIndex (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> ℕ -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop


def GenericTableConstraint := TraceOfLength N M (F p) -> List (Expression N M (F p))

/--
  A RowConstraint is a constraint that applies to a single row in the table
-/
def RowConstraint := Row N (F p) -> ConstraintGadget p N M

/--
  A TwoRowsConstraint is a constraint that applies to two rows in the table
-/
def TwoRowsConstraint := Row N (F p) -> Row N (F p) -> ConstraintGadget p N M

/--
  Apply a row constraint to some specific row of the table
-/
def applyBoundary (n : ℕ) (c : RowConstraint N M p) : GenericTableConstraint N M p :=
  fun trace => inner c trace.val
  where
  inner (c : RowConstraint N M p) : Trace N (F p) -> List (Expression N M (F p))
  | <+> => []
  | rest +> row => if rest.len = n then fullConstraintSet (c row) else inner c rest

/--
  Apply a single row constraint to every row of the table
-/
def applyEveryRowSingleRow (c : RowConstraint N M p) : GenericTableConstraint N M p :=
  fun trace => inner c trace.val
  where
  inner (c : RowConstraint N M p) : Trace N (F p) -> List (Expression N M (F p))
  | <+> => []
  | rest +> row => fullConstraintSet (c row) ++ inner c rest

/--
  Apply a two rows constraint to every row of the table
-/
def applyEveryRowTwoRows (c : TwoRowsConstraint N M p) [Fact (M ≥ 2)] : GenericTableConstraint N M p :=
  fun trace => inner c trace.val
  where
  -- TODO: make inner type safe by removing the empty and one line cases, proving to the
  -- type checker that if M >= 2 then those cases are not needed
  inner (c : TwoRowsConstraint N M p) : Trace N (F p) -> List (Expression N M (F p))
  -- empty trace
  | <+> => []
  -- single line trace: do not apply constraint
  | <+> +> _ => []
  -- at least two lines: apply constraint to every row
  | rest +> curr +> next => fullConstraintSet (c curr next) ++ inner c (rest +> curr)

/--
  Table constraint definition. A table constraint can be either
  - a boundary constraint, which applies to a specific row in the table
  - a "every row single row" constraint, which is defined over a row and applies to every row
  - a "every row two rows" constraint, which is defined over two adjacent rows and applies to every row
-/
inductive TableConstraint where
  | boundary : ℕ -> (RowConstraint N M p) -> TableConstraint
  | everyRowSingleRow : (RowConstraint N M p) -> TableConstraint
  | everyRowTwoRows : (Fact (M ≥ 2)) -> (TwoRowsConstraint N M p) -> TableConstraint


def GenericTableLookup := TraceOfLength N M (F p) -> List (LookupArgument p N M)

/--
  Apply a lookup assumption to every row of the table
-/
def lookupEveryRow (c : Row N (F p) -> LookupArgument p N M) : GenericTableLookup N M p :=
  fun trace => inner c trace.val
  where
  inner (c : Row N (F p) -> LookupArgument p N M) : Trace N (F p) -> List (LookupArgument p N M)
  | <+> => []
  | rest +> row => [(c row)] ++ inner c rest

inductive TableLookup where
  | everyRow : (Row N (F p) -> LookupArgument p N M) -> TableLookup


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
  spec : TraceOfLength N M (F p) -> Prop
  equiv :
    ∀ trace : TraceOfLength N M (F p),
    (forallList lookups (fun c => match c with
      | TableLookup.everyRow lookup =>
        forallList ((lookupEveryRow N M p lookup) trace) (λ c => c.prop trace))
    )
    ->
    (
      (forallList constraints (fun c => match c with
        | TableConstraint.boundary idx c
            => forallList ((applyBoundary N M p idx c) trace) (fun constraint => trace.eval constraint = 0)
        | TableConstraint.everyRowSingleRow c
            => forallList ((applyEveryRowSingleRow N M p c) trace) (fun constraint => trace.eval constraint = 0)
        | TableConstraint.everyRowTwoRows _ c
            => forallList ((applyEveryRowTwoRows N M p c) trace) (fun constraint => trace.eval constraint = 0))
      )
      ↔
      spec trace
    )


end Table
