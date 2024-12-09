import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Circuit
variable {p : ℕ} [Fact p.Prime] {F: Type} [CommRing F]

structure Variable (F : Type) where
  index: ℕ
  witness: Unit → F

instance : Repr (Variable F) where
  reprPrec v _ := "x" ++ repr v.index

inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
deriving Repr

structure Vector (F : Type) (n: ℕ) where
  entries: Fin n → F

structure Table (F : Type) where
  arity: ℕ
  length: ℕ
  row: Fin length → Vector F arity

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  witness: Unit → Fin table.length -- index of the entry

inductive Row
  | Current
  | Next

structure Cell (F : Type) where
  column: ℕ -- index of the column
  row: Row

structure Context (F : Type) where
  locals: Array (Variable F)
  constraints: Array (Expression F)
  lookups: Array (Lookup F)
  assignments: Array (Cell F × Variable F)

inductive Operation (F : Type) where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : (Unit → Context F) → Operation F

def Transcript (F : Type) := List (Operation F)
def State (F : Type) := Context F × Transcript F

-- operations we can do in a circuit

-- create a new variable
def witness (ctx: Context F) (compute : Unit → F) : (Context F × Operation F) × Variable F :=
  let index := ctx.locals.size
  let var: Variable F := ⟨ index, compute ⟩
  (⟨ { ctx with locals := ctx.locals.push var }, Operation.Witness compute⟩, var)

-- add a constraint
def assert (ctx: Context F) (e: Expression F) : Context F × Operation F :=
  ⟨{ ctx with constraints := ctx.constraints.push e }, Operation.Assert e⟩

-- add a lookup
def lookup (ctx: Context F) (l: Lookup F) : Context F × Operation F :=
  ⟨{ ctx with lookups := ctx.lookups.push l }, Operation.Lookup l ⟩

-- assign a variable to a cell
def assign (ctx: Context F) (c: Cell F) (v: Variable F) : Context F × Operation F :=
  ⟨{ ctx with assignments := ctx.assignments.push (c, v) }, Operation.Assign (c, v)⟩

-- run a sub-circuit
def subcircuit (ctx: Context F) (c: Unit → Context F) : Context F × Operation F :=
  ⟨ctx, Operation.Circuit c⟩

namespace Expression
def eval : Expression F → F
  | var v => v.witness ()
  | const c => c
  | add x y => eval x + eval y
  | mul x y => eval x * eval y
end Expression
