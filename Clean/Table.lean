import Clean.Utils.Field
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section Table
variable (N : ℕ+) (M : ℕ) (p : ℕ) [Fact p.Prime]


def forAllRowsOfTrace (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

def forAllRowsOfTraceWithIndex (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> ℕ -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop


def GenericTableConstraint := TraceOfLength N M (F p) -> List (Expression N M (F p))

def RowConstraint := Row N (F p) -> ConstraintGadget p N M
def TwoRowsConstraint := Row N (F p) -> Row N (F p) -> ConstraintGadget p N M

def applyBoundary (n : ℕ) (c : RowConstraint N M p) : GenericTableConstraint N M p :=
  fun trace => inner c trace.val
  where
  inner (c : RowConstraint N M p) : Trace N (F p) -> List (Expression N M (F p))
  | <+> => []
  | rest +> row => if rest.len = n then fullConstraintSet (c row) else inner c rest

def applyEveryRowSingleRow (c : RowConstraint N M p) : GenericTableConstraint N M p :=
  fun trace => inner c trace.val
  where
  inner (c : RowConstraint N M p) : Trace N (F p) -> List (Expression N M (F p))
  | <+> => []
  | rest +> row => fullConstraintSet (c row) ++ inner c rest

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

def GenericTableLookup := TraceOfLength N M (F p) -> List (LookupArgument p N M)

def lookupEveryRow (c : Row N (F p) -> LookupArgument p N M) : GenericTableLookup N M p :=
  fun trace => inner c trace.val
  where
  inner (c : Row N (F p) -> LookupArgument p N M) : Trace N (F p) -> List (LookupArgument p N M)
  | <+> => []
  | rest +> row => [(c row)] ++ inner c rest

inductive TableLookup where
  | everyRow : (Row N (F p) -> LookupArgument p N M) -> TableLookup

inductive TableConstraint where
  | boundary : ℕ -> (RowConstraint N M p) -> TableConstraint
  | everyRowSingleRow : (RowConstraint N M p) -> TableConstraint
  | everyRowTwoRows : (Fact (M ≥ 2)) -> (TwoRowsConstraint N M p) -> TableConstraint

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
