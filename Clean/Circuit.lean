import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Circuit
variable {F: Type}

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

namespace Expression
variable [CommRing F]

def eval : Expression F → F
  | var v => v.witness ()
  | const c => c
  | add x y => eval x + eval y
  | mul x y => eval x * eval y

def toString [Repr F] : Expression F → String
  | var v => reprStr v
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e

-- combine expressions elegantly
instance : Zero (Expression F) where
  zero := const 0

instance : One (Expression F) where
  one := const 1

instance : Add (Expression F) where
  add := add

instance : Neg (Expression F) where
  neg e := mul (const (-1)) e

instance : Sub (Expression F) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (Expression F) where
  mul := mul

instance : Coe F (Expression F) where
  coe f := const f

instance : Coe (Variable F) (Expression F) where
  coe x := var x

instance : Coe (Expression F) F where
  coe x := x.eval

instance : HMul F (Expression F) (Expression F) where
  hMul := fun f e => mul f e
end Expression

def Row (F : Type) (n: ℕ) := { l: List F // l.length = n }
def row (l: List F) : Row F l.length := ⟨ l, rfl ⟩

instance [Repr F] {n: ℕ} : Repr (Row F n) where
  reprPrec l _ := repr l.val

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → { l: List F // l.length = arity }

structure Lookup (F : Type) where
  table: Table F
  entry: Row (Expression F) table.arity
  index: Unit → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

inductive RowIndex
  | Current
  | Next
deriving Repr

structure Cell (F : Type) where
  row: RowIndex
  column: ℕ -- index of the column
deriving Repr

structure Context (F : Type) where
  offset: ℕ
  locals: Array (Variable F)
  constraints: Array (Expression F)
  lookups: Array (Lookup F)
  assignments: Array (Cell F × Variable F)
deriving Repr

namespace Context
def empty (offset: ℕ) : Context F := ⟨ offset, #[] , #[] , #[] , #[] ⟩
end Context

variable {α : Type}

inductive Operation (F : Type) where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : Context F × List (Operation F) → Operation F

namespace Operation

def run (ctx: Context F) : Operation F → Context F
  | Witness compute =>
    let var := ⟨ ctx.offset, compute ⟩
    let offset := ctx.offset + 1
    { ctx with offset, locals := ctx.locals.push var }
  | Assert e => { ctx with constraints := ctx.constraints.push e }
  | Lookup l => { ctx with lookups := ctx.lookups.push l }
  | Assign (c, v) => { ctx with assignments := ctx.assignments.push (c, v) }
  | Circuit ⟨ subctx, _ops ⟩ =>
    -- TODO probably want to import more stuff from the subcontext
    { ctx with offset := subctx.offset }

def toString [Repr F] : (op : Operation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
  | Circuit ⟨ _, ops ⟩ => "(Circuit " ++ reprStr (go ops) ++ ")"
-- this helps lean recognize the structural recursion
where go (ops : List (Operation F)) : List String :=
  match ops with
  | [] => []
  | op :: ops => op.toString :: go ops

instance [Repr F] : ToString (Operation F) where
  toString := toString
end Operation

def Stateful (F : Type) (α : Type) := Context F → (Context F × List (Operation F)) × α

instance : Monad (Stateful F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

def Stateful.run (circuit: Stateful F Unit) (offset: ℕ := 0) : Context F × List (Operation F) :=
  let ctx := Context.empty offset
  let ((ctx, ops), _ ) := circuit ctx
  (ctx, ops)

def as_stateful (f: Context F → Operation F × α) : Stateful F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := Operation.run ctx op
  (⟨ ctx', [op] ⟩, a)

-- operations we can do in a circuit

-- create a new variable
def witness_var (compute : Unit → F) := as_stateful (fun ctx =>
  let var: Variable F := ⟨ ctx.offset, compute ⟩
  (Operation.Witness compute, var)
)

def witness (compute : Unit → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
def assert_zero (e: Expression F) := as_stateful (
  fun _ => (Operation.Assert e, ())
)

-- add a lookup
def lookup (l: Lookup F) := as_stateful (
  fun _ => (Operation.Lookup l, ())
)

-- assign a variable to a cell
def assign_cell (c: Cell F) (v: Variable F) := as_stateful (
  fun _ => (Operation.Assign (c, v), ())
)

-- run a sub-circuit
def subcircuit (circuit: Stateful F α) := as_stateful (
  fun ctx =>
    let subctx := Context.empty ctx.offset
    let (state, a) := circuit subctx
    (Operation.Circuit state, a)
)

-- TODO derived operations: assert(lhs == rhs), <== (witness + assert)

def to_var [CommRing F] (x: Expression F) : Stateful F (Variable F) :=
  match x with
  | Expression.var v => pure v
  | x => do
    let x' ← witness_var (fun _ => x.eval)
    assert_zero (x - (Expression.var x'))
    return x'

structure InputCell (F : Type) where
  cell: { cell: Cell F // cell.row = RowIndex.Current }
  var: Variable F

def InputCell.set_next [CommRing F] (c: InputCell F) (v: Expression F) := do
  let v' ← to_var v
  assign_cell { c.cell.val with row := RowIndex.Next } v'

def create_input (value: F) (column: ℕ) : Stateful F (InputCell F) := do
  let var ← witness_var (fun _ => value)
  let cell: Cell F := ⟨ RowIndex.Current, column ⟩
  let input: InputCell F := ⟨ ⟨ cell, rfl ⟩, var ⟩
  return input

instance : Coe (InputCell F) (Variable F) where
  coe x := x.var

end Circuit

section -- examples
open Circuit
open Circuit.Expression (const)

-- general Fp helpers
variable {p: ℕ} [p_pos: Fact (p ≠ 0)]

def F p := ZMod p
instance : CommRing (F p) := ZMod.commRing p

def create (x: ℕ) (lt: x < p) : F p :=
  match p with
  | 0 => False.elim (Nat.not_lt_zero x lt)
  | _ + 1 => ⟨ x, lt ⟩

def less_than_p (x: F p) : x.val < p := by
  rcases p
  · have : 0 ≠ 0 := p_pos.elim; tauto
  · exact x.is_lt

-- boolean type

def assert_bool (x: Expression (F p)) := do
  assert_zero (x * (x - 1))

inductive Boolean (F: Type) where
  | private mk : (Variable F) → Boolean F

namespace Boolean
def var (b: Boolean (F p)) := Expression.var b.1

def witness (compute : Unit → F p) := do
  let x ← witness_var compute
  assert_bool x
  return Boolean.mk x

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var
end Boolean


-- byte type
variable [p_large_enough: Fact (p > 512)]

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  create (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod_256 (x: F p) : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv (x: F p) (c: ℕ+) : F p :=
  create (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])

def from_byte (x: Fin 256) : F p :=
  create x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteTable : Table (F p) where
  name := "Bytes"
  length := 256
  arity := 1
  row i := row [from_byte i]

def byte_lookup (x: F p) := lookup {
  table := ByteTable
  entry := row [const x]
  index := fun () =>
    if h : (x.val < 256)
    then ⟨x.val, h⟩
    else ⟨0, by show 0 < 256; norm_num⟩
}

inductive Byte (F: Type) where
  | private mk : (Variable F) → Byte F

namespace Byte
def var (b: Byte (F p)) := Expression.var b.1

def witness (compute : Unit → F p) := do
  let x ← witness_var compute
  byte_lookup x
  return Byte.mk x

instance : Coe (Byte (F p)) (Expression (F p)) where
  coe x := x.var
end Byte

def Add8 (x y: Expression (F p)) : Stateful (F p) (Expression (F p)) := do
  let z ← witness (fun () => mod_256 (x + y))
  byte_lookup z
  let carry ← witness (fun () => floordiv (x + y) 256)
  assert_bool carry

  assert_zero (x + y - z - carry * (const 256))
  return z

def Main (x y : F p) : Stateful (F p) Unit := do
  -- in a real AIR definition, these could be inputs to every step
  let x ← create_input x 0
  let y ← create_input y 1

  let z ← subcircuit (Add8 x y)
  x.set_next y
  y.set_next z

#eval!
  let p := 1009
  let p_non_zero := Fact.mk (by norm_num : p ≠ 0)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let main := Main (x := (20 : F p)) (y := 30)
  let (_, ops) := main.run
  ops
end

-- this would only be needed if we did inversion somewhere
-- theorem prime_1009 : Nat.Prime 1009 := by
--   set_option maxRecDepth 900 in decide
