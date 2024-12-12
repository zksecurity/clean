import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector

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
variable [Field F]

@[simp]
def eval : Expression F → F
  | var v => v.witness ()
  | const c => c
  | add x y => eval x + eval y
  | mul x y => eval x * eval y

/--
Evaluate expression given an external `environment` that determines the assignment
of all variables.

This is needed when we want to make statements about a circuit in the adversarial
situation where the prover can assign anything to variables.
-/
@[simp]
def eval_env (env: ℕ → F) : Expression F → F
  | var v => env v.index
  | const c => c
  | add x y => eval_env env x + eval_env env y
  | mul x y => eval_env env x * eval_env env y

def toString [Repr F] : Expression F → String
  | var v => "x" ++ reprStr v.index
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

instance [Repr F] {n: ℕ} : Repr (Vector F n) where
  reprPrec l _ := repr l.val

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → { l: List F // l.length = arity }

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
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
deriving Repr

namespace Context
@[simp]
def empty : Context F := ⟨ 0, #[] ⟩
end Context

variable {α : Type} [Field F]

inductive PreOperation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → PreOperation F
  | Assert : Expression F → PreOperation F
  | Lookup : Lookup F → PreOperation F
  | Assign : Cell F × Variable F → PreOperation F

namespace PreOperation
def constraints_hold (env: ℕ → F) : List (PreOperation F) → Prop
  | [] => True
  | op :: [] => match op with
    | PreOperation.Assert e => (e.eval_env env) = 0
    | _ => True
  | op :: ops => match op with
    | PreOperation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold env ops
    | _ => constraints_hold env ops
end PreOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SpecImplied (F: Type) [Field F] where
  ops: List (PreOperation F)
  spec: Prop
  imply_spec: ∀ env, (PreOperation.constraints_hold env ops) → spec

inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : SpecImplied F → Operation F
namespace Operation

@[simp]
def run (ctx: Context F) : Operation F → Context F
  | Witness compute =>
    let var := ⟨ ctx.offset, compute ⟩
    let offset := ctx.offset + 1
    { ctx with offset, locals := ctx.locals.push var }
  | Assert _ => ctx
  | Lookup _ => ctx
  | Assign _ => ctx
  | Circuit _ => ctx

def toString [Repr F] : (op : Operation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
  -- | Circuit ⟨ _, ops ⟩ => "(Circuit " ++ reprStr (go ops) ++ ")"
  | Circuit _ => "Circuit"
-- this helps lean recognize the structural recursion
where go (ops : List (Operation F)) : List String :=
  match ops with
  | [] => []
  | op :: ops => op.toString :: go ops

instance [Repr F] : ToString (Operation F) where
  toString := toString
end Operation

@[simp]
def Stateful (F : Type) [Field F] (α : Type) := Context F → (Context F × List (Operation F)) × α

instance : Monad (Stateful F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

@[simp]
def Stateful.run (circuit: Stateful F α) : Context F × List (Operation F) × α :=
  let ((ctx, ops), a) := circuit Context.empty
  (ctx, ops, a)

@[simp]
def as_stateful (f: Context F → Operation F × α) : Stateful F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := Operation.run ctx op
  ((ctx', [op]), a)

def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => PreOperation.Witness compute :: to_flat_operations ops
    | Operation.Assert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.Lookup l => PreOperation.Lookup l :: to_flat_operations ops
    | Operation.Assign (c, v) => PreOperation.Assign (c, v) :: to_flat_operations ops
    | Operation.Circuit ⟨ ops', _, _ ⟩ => ops' ++ to_flat_operations ops

-- operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Unit → F) := as_stateful (fun ctx =>
  let var: Variable F := ⟨ ctx.offset, compute ⟩
  (Operation.Witness compute, var)
)

@[simp]
def witness (compute : Unit → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) := as_stateful (
  fun _ => (Operation.Assert e, ())
)

-- add a lookup
@[simp]
def lookup (l: Lookup F) := as_stateful (
  fun _ => (Operation.Lookup l, ())
)

-- assign a variable to a cell
@[simp]
def assign_cell (c: Cell F) (v: Variable F) := as_stateful (
  fun _ => (Operation.Assign (c, v), ())
)

-- TODO derived operations: assert(lhs == rhs), <== (witness + assert)

def to_var [Field F] (x: Expression F) : Stateful F (Variable F) :=
  match x with
  | Expression.var v => pure v
  | x => do
    let x' ← witness_var (fun _ => x.eval)
    assert_zero (x - (Expression.var x'))
    return x'

structure InputCell (F : Type) where
  cell: { cell: Cell F // cell.row = RowIndex.Current }
  var: Variable F

def InputCell.set_next [Field F] (c: InputCell F) (v: Expression F) := do
  let v' ← to_var v
  assign_cell { c.cell.val with row := RowIndex.Next } v'

def create_input (value: F) (column: ℕ) : Stateful F (InputCell F) := do
  let var ← witness_var (fun _ => value)
  let cell: Cell F := ⟨ RowIndex.Current, column ⟩
  assign_cell cell var
  let input: InputCell F := ⟨ ⟨ cell, rfl ⟩, var ⟩
  return input

instance : Coe (InputCell F) (Variable F) where
  coe x := x.var

-- extract information from circuits by running them
inductive NestedList (α : Type) :=
  | scalar : α → NestedList α
  | list : List (NestedList α) → NestedList α
deriving Repr

def constraints' : List (PreOperation F) → List (NestedList (Expression F))
  | [] => []
  | op :: ops => match op with
    | PreOperation.Assert e => NestedList.scalar e :: constraints' ops
    | _ => constraints' ops

def constraints : List (Operation F) →  List (NestedList (Expression F))
  | [] => []
  | op :: ops => match op with
    | Operation.Assert e => NestedList.scalar e :: constraints ops
    | Operation.Circuit ⟨ ops', _, _ ⟩ => NestedList.list (constraints' ops') :: constraints ops
    | _ => constraints ops

def witness_length (circuit : Stateful F α) : ℕ :=
  let (ctx, _, _) := circuit.run
  ctx.locals.size

namespace Adversarial
  @[simp]
  def constraints_hold_from_list [Field F] (env: (ℕ → F)) : List (Operation F) → Prop
    | [] => True
    | op :: ops => match op with
      | Operation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold_from_list env ops
      | Operation.Circuit ⟨ _, spec, _ ⟩ => spec ∧ constraints_hold_from_list env ops
      | _ => constraints_hold_from_list env ops

  @[simp]
  def constraints_hold [Field F] (env: (ℕ → F)) (circuit: Stateful F α)   : Prop :=
    let (_, ops, _) := circuit.run
    constraints_hold_from_list env ops
end Adversarial

@[simp]
def constraints_hold_from_list [Field F] : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => e.eval = 0
    | Operation.Circuit ⟨ _, spec, _ ⟩ => spec
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (e.eval = 0) ∧ constraints_hold_from_list ops
    | Operation.Circuit ⟨ _, spec, _ ⟩ => spec ∧ constraints_hold_from_list ops
    | _ => constraints_hold_from_list ops

@[simp]
def constraints_hold (circuit: Stateful F α) : Prop :=
  let (_, ops, _) := circuit.run
  constraints_hold_from_list ops

def output (circuit: Stateful F α) : α :=
  let (_, _, a) := circuit.run
  a

-- class of types that are composed of variables,
-- and can be evaluated into something that is composed of field elements
class ProvableType (F: Type) (α_var : Type) (α_value : Type) where
  size : ℕ

  to_vars : α_var → Vector (Expression F) size
  from_vars : Vector (Expression F) size → α_var

  to_values : α_value → Vector F size
  from_values : Vector F size → α_value

variable {α_var α_value β_var β_value: Type}

namespace ProvableType
def eval [ProvableType F α_var α_value] (x: α_var) : α_value :=
  let n := ProvableType.size F α_var α_value
  let vars : Vector (Expression F) n := ProvableType.to_vars x
  let values := vars.map (fun v => v.eval)
  ProvableType.from_values values

def eval_env [ProvableType F α_var α_value] (env: ℕ → F) (x: α_var) : α_value :=
  let n := ProvableType.size F α_var α_value
  let vars : Vector (Expression F) n := ProvableType.to_vars x
  let values := vars.map (fun v => v.eval_env env)
  ProvableType.from_values values

def const [ProvableType F α_var α_value] (x: α_value) : α_var :=
  let n := ProvableType.size F α_var α_value
  let values : Vector F n := ProvableType.to_values x
  ProvableType.from_vars (values.map (fun v => Expression.const v))
end ProvableType

-- goal: define circuit such that we can provably use it as subcircuit
structure FormalCircuit [ProvableType F α_var α_value] [ProvableType F β_var β_value] where
  main: β_var → Stateful F α_var

  assumptions: β_value → Prop
  spec: β_value → α_value → Prop

  soundness: open ProvableType in
    ∀ b : β_value, let b_var: β_var := const (F:=F) b
    assumptions b →
    ∃ a : α_value,
    (∃ env,
      Adversarial.constraints_hold env (main b_var)
      ∧ (eval_env env (output (main b_var)) = a))
    → spec b a

  completeness: open ProvableType in
    ∀ b : β_value, assumptions b →
    constraints_hold (main (const (F:=F) b))


-- def formal_circuit_is_subcircuit
--   (circuit: FormalCircuit (F := F) β α) (b : β) (assumptions: circuit.assumptions b) :
--   Circuit.SpecImplied F :=
--   let main := circuit.main b
--   let ((ctx, ops), a) := main Context.empty
--   let ops := main.run
--   let spec := circuit.spec b
--   let soundness := circuit.soundness b
--   let completeness := circuit.completeness b

--   ⟨ to_flat_operations, spec, fun env ops => soundness assumptions env ops ⟩

-- run a sub-circuit
-- @[simp]
-- def subcircuit (circuit: Stateful F α) (spec: Prop) () := as_stateful (
--   fun ctx =>
--     let subctx := Context.empty ctx.offset
--     let ((ctx, ops), a) := circuit subctx
--     let flat_ops := to_flat_operations ops

--     (Operation.Circuit state, a)
-- )
end Circuit



section -- examples
open Circuit
open Circuit.Expression (const)

-- general Fp helpers
variable {p: ℕ} [Fact p.Prime]

def F p := ZMod p
instance isField : Field (F p) := ZMod.instField p
instance : CommRing (F p) := isField.toCommRing

def create (n: ℕ) (lt: n < p) : F p :=
  match p with
  | 0 => False.elim (Nat.not_lt_zero n lt)
  | _ + 1 => ⟨ n, lt ⟩

def less_than_p [p_pos: Fact (p ≠ 0)] (x: F p) : x.val < p := by
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

def spec (x: F p) := x = 0 ∨ x = 1

theorem dsimp_equiv : ∀ x: F p,
  x * (x + -1 * 1) = 0 ↔ x = 0 ∨ x = 1 :=
by
  intro x
  simp
  show x = 0 ∨ x + -1 = 0 ↔ x = 0 ∨ x = 1
  suffices x + -1 = 0 ↔ x = 1 by tauto
  constructor
  · intro (h : x + -1 = 0)
    show x = 1
    calc x
    _ = (x + -1) + 1 := by ring
    _ = 1 := by simp [h]
  · intro (h : x = 1)
    show x + -1 = 0
    simp [h]

theorem equiv : ∀ x: F p,
  constraints_hold (assert_bool (const x)) ↔ spec x
:= by
  -- simplify
  dsimp
  show ∀ (x : F p), x * (x + -1 * 1) = 0 ↔ spec x

  -- proof
  exact dsimp_equiv
end Boolean


-- byte type
variable [p_large_enough: Fact (p > 512)]

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  create (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod_256 (x: F p) : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv [Fact (p ≠ 0)] (x: F p) (c: ℕ+) : F p :=
  create (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])

def from_byte (x: Fin 256) : F p :=
  create x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteTable : Table (F p) where
  name := "Bytes"
  length := 256
  arity := 1
  row i := vector [from_byte i]

def byte_lookup (x: Expression (F p)) := lookup {
  table := ByteTable
  entry := vector [x]
  index := fun () =>
    let x := x.eval.val
    if h : (x < 256)
    then ⟨x, h⟩
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

def witness_or_trace_var (trace: Option (ℕ → F p)) (compute : Unit → F p) := as_stateful (fun ctx =>
  let i := ctx.offset
    let compute' := fun () => match trace with
    | none => compute ()
    | some trace => trace i
  let var: Variable (F p) := ⟨ i, compute' ⟩
  (Operation.Witness compute', var)
)
def witness_or_value_var (value: Option (F p)) (compute : Unit → F p) := as_stateful (fun ctx =>
  let i := ctx.offset
    let compute' := fun () => match value with
    | none => compute ()
    | some v => v
  let var: Variable (F p) := ⟨ i, compute' ⟩
  (Operation.Witness compute', var)
)

def witness_or_trace (trace: Option (ℕ → F p)) (compute: Unit → F p) := do
  let var ← witness_or_trace_var trace compute
  return Expression.var var

def witness_or_value (value: Option (F p)) (compute: Unit → F p) := do
  let var ← witness_or_value_var value compute
  return Expression.var var

variable [Fact (p ≠ 0)]

def Add8 (x y: Expression (F p)) (z carry: Option (F p) := none) := do
  let z ← witness_or_value z (fun () => mod_256 (x + y))
  byte_lookup z
  let carry ← witness_or_value carry (fun () => floordiv (x + y) 256)
  assert_bool carry

  assert_zero (x + y - z - carry * (const 256))
  return z

namespace Add8
def spec (x y z: F p) := (z.val < 256) → z.val = (x.val + y.val) % 256

theorem soundness : ∀ x y : F p, -- inputs/outputs
  x.val < 256 → y.val < 256 → -- assumptions
  ∀ z : F p, -- output
  (∃ carry : F p, constraints_hold (Add8 (const x) (const y) (some z) (some carry))) -- circuit
  → spec x y z
:= by
  -- simplify
  intro x y hx hy z ⟨carry, h⟩
  dsimp at h
  dsimp [spec]

  guard_hyp h: (carry * (carry + -1 * 1) = 0) ∧ (x + y + -1 * z + -1 * (carry * 256) = 0)
  show (z.val < 256) → z.val = (x.val + y.val) % 256

  -- proof
  rcases h with ⟨h_bool, h_add⟩

  -- reuse Boolean.equiv
  have spec_bool: carry = 0 ∨ carry = 1 := (Boolean.equiv carry).mp h_bool

  sorry
end Add8

def Main (x y : F p) : Stateful (F p) Unit := do
  -- in a real AIR definition, these could be inputs to every step
  let x ← create_input x 0
  let y ← create_input y 1

  let z ← Add8 x y
  x.set_next y
  y.set_next z

#eval
  let p := 1009
  let p_prime := Fact.mk prime_1009
  let p_non_zero := Fact.mk (by norm_num : p ≠ 0)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let main := Main (x := (20 : F p)) (y := 30)
  let (_, ops, _) := main.run
  ops
end
