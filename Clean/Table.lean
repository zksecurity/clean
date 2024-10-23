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
  Apply a row constraint to a single row
-/
def applySingleRowConstraint (c : RowConstraint N M p) (row : Row N (F p)) : List (Expression N M (F p)) :=
  fullConstraintSet (c row)

/--
  Apply a two rows constraint to two adjacent rows
-/
def applyTwoRowConstraint [Fact (M ≥ 2)] (c : TwoRowsConstraint N M p) (curr : Row N (F p)) (next : Row N (F p)) : List (Expression N M (F p)) :=
  fullConstraintSet (c curr next)

/--
  Table constraint definition. A table constraint can be either
  - a boundary constraint, which applies to a specific row in the table
  - a "every row single row" constraint, which is defined over a row and applies to every row
  - a "every row two rows" constraint, which is defined over two adjacent rows and applies to every row,
    except the last one
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
  Compute the full set of constraints that are implied by a table constraint, so that they are applied
  with an inductive structure to every row in the table.
-/
def fullTableConstraintSet (constraints : List (TableConstraint N M p)) (trace: TraceOfLength N M (F p)) : List (Expression N M (F p)) :=
  foldl constraints trace.val constraints
  where
  /--
  The foldl function applies the constraints to the trace inductively on the trace

  We want to write something like:
  for row in trace:
    for constraint in constraints:
      apply constraint to row
  in this exact order, so that the inductive structure is at the top-level.

  This construction is quite involved but is simplifies a lot inductive proofs.
  We do double induction: first on the trace, then on the constraints: we apply every constraint to the current row, and
  then recurse on the rest of the trace.
  `cs` is the list of constraints that we have to apply and it is never changed during the induction
  `cs_iterator` is walked inductively for every row.
  Once the `cs_iterator` is empty, we start again on the rest of the trace with the initial constraints `cs` -/
  foldl (cs : List (TableConstraint N M p)) : Trace N (F p) -> (cs_iterator: List (TableConstraint N M p)) -> List (Expression N M (F p))

    -- if the trace has at least two rows and the constraint is a "every row two rows" constraint, we apply the constraint
    | trace +> curr +> next, (TableConstraint.everyRowTwoRows _ c)::rest =>
        (applyTwoRowConstraint N M p c curr next) ++ foldl cs (trace +> curr +> next) rest

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableConstraint.boundary idx c)::rest =>
        (if trace.len = idx then applySingleRowConstraint N M p c row else []) ++ foldl cs (trace +> row) rest

    -- if the trace has at least one row and the constraint is a "every row single row" constraint, we apply the constraint
    | trace +> row, (TableConstraint.everyRowSingleRow c)::rest =>
        applySingleRowConstraint N M p c row ++ foldl cs (trace +> row) rest

    -- if the trace has not enough rows for the "every row two rows" constraint, we skip the constraint
    -- TODO: this is fine if the trace length M is >= 2, but we should check this somehow
    | trace, (TableConstraint.everyRowTwoRows _ _)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => []

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
      (forallList (fullTableConstraintSet N M p constraints trace) (fun constraint => trace.eval constraint = 0))
      ↔
      spec trace
    )


end Table
