import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable

namespace Circuit
variable {F: Type}

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → Vector F arity

def Table.contains (table: Table F) row := ∃ i, row = table.row i

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
def toString [Repr F] : (op : PreOperation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"

def constraints_hold (env: ℕ → F) : List (PreOperation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Assert e => (e.eval_env env) = 0
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env))
    | _ => True
  | op :: ops => match op with
    | PreOperation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold env ops
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold env ops
    | _ => constraints_hold env ops
end PreOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F]
  (soundness: Prop) (completeness: Prop)
where
  ops: List (PreOperation F)

  input_size: ℕ
  output_size: ℕ
  input: Vector (Expression F) input_size
  assumptions: Vector F input_size → Prop
  output: Vector (Expression F) output_size

  imply_soundness :
    ∀ input_value : Vector F input_size,
    ∀ env : ℕ → F,
    input.map (Expression.eval_env env) = input_value →
    assumptions input_value →
    PreOperation.constraints_hold env ops →
    soundness

  imply_completeness :
    ∀ input_value : Vector F input_size,
    ∀ env : ℕ → F,
    input.map (Expression.eval_env env) = input_value →
    assumptions input_value →
    completeness →
    PreOperation.constraints_hold env ops

inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  -- an assertion that ends up in the list of constraints, but is IGNORED by `constraints_hold`
  -- we need this in soundness proofs to weaken our statement, by ignoring witnesses the prover can't override
  | SilentAssert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : (Σ soundness : Prop, Σ completeness : Prop, SubCircuit F soundness completeness) → Operation F
namespace Operation

@[simp]
def run (ctx: Context F) : Operation F → Context F
  | Witness compute =>
    let var := ⟨ ctx.offset, compute ⟩
    let offset := ctx.offset + 1
    { ctx with offset, locals := ctx.locals.push var }
  | Assert _ => ctx
  | SilentAssert _ => ctx
  | Lookup _ => ctx
  | Assign _ => ctx
  | Circuit ⟨ _, _, circuit ⟩ =>
    let offset := ctx.offset + circuit.ops.length
    { ctx with offset }

def toString [Repr F] : (op : Operation F) → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | SilentAssert e => "(SilentAssert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
  | Circuit ⟨ _, _, circuit ⟩ => "(Circuit " ++ reprStr (circuit.ops.map PreOperation.toString) ++ ")"

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
def Stateful.run (circuit: Stateful F α) : List (Operation F) × α :=
  let ((_, ops), a) := circuit Context.empty
  (ops, a)

@[simp]
def as_stateful (f: Context F → Operation F × α) : Stateful F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := Operation.run ctx op
  ((ctx', [op]), a)

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

@[simp]
def assert_zero_silent (e: Expression F) := as_stateful (
  fun _ => (Operation.SilentAssert e, ())
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
    | Operation.Circuit ⟨ _, _, circuit⟩ => NestedList.list (constraints' circuit.ops) :: constraints ops
    | _ => constraints ops

def witness_length (circuit : Stateful F α) : ℕ :=
  let ((ctx, _), _) := circuit Context.empty
  ctx.locals.size

namespace Adversarial
  @[simp]
  def constraints_hold_from_list [Field F] (env: (ℕ → F)) : List (Operation F) → Prop
    | [] => True
    | op :: [] => match op with
      | Operation.Assert e => (e.eval_env env) = 0
      | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env env))
      | Operation.Circuit ⟨ soundness, _, _ ⟩ => soundness
      | _ => True
    | op :: ops => match op with
      | Operation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold_from_list env ops
      | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold_from_list env ops
      | Operation.Circuit ⟨ soundness, _, _ ⟩ => soundness ∧ constraints_hold_from_list env ops
      | _ => constraints_hold_from_list env ops

  @[simp]
  def constraints_hold [Field F] (env: (ℕ → F)) (circuit: Stateful F α)   : Prop :=
    constraints_hold_from_list env (circuit Context.empty).1.2

  def to_flat_operations [Field F] (ops: List (Operation F)) : List (PreOperation F) :=
  match ops with
  | [] => []
  | op :: ops => match op with
    | Operation.Witness compute => PreOperation.Witness compute :: to_flat_operations ops
    | Operation.Assert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.SilentAssert e => PreOperation.Assert e :: to_flat_operations ops
    | Operation.Lookup l => PreOperation.Lookup l :: to_flat_operations ops
    | Operation.Assign (c, v) => PreOperation.Assign (c, v) :: to_flat_operations ops
    | Operation.Circuit ⟨ _, _, circuit ⟩ => circuit.ops ++ to_flat_operations ops

  -- TODO super painful, mainly because `cases` doesn't allow rich patterns -- how does this work again?
  theorem can_flatten_first : ∀ (env: ℕ → F) (ops: List (Operation F)),
    PreOperation.constraints_hold env (to_flat_operations ops)
    → constraints_hold_from_list env ops
  := by
    intro env ops
    induction ops with
    | nil => intro h; exact h
    | cons op ops ih =>
      cases ops with
      | nil =>
        simp at ih
        cases op with
        | Circuit c =>
          sorry
        | _ => simp [PreOperation.constraints_hold]
      | cons op' ops' =>
        let ops := op' :: ops'
        cases op with
        | Circuit c => sorry
        | Assert e => sorry
        | SilentAssert e => sorry
        | Witness c =>
          have h_ops : to_flat_operations (Operation.Witness c :: op' :: ops') = PreOperation.Witness c :: to_flat_operations (op' :: ops') := rfl
          rw [h_ops]
          intro h_pre
          have h1 : PreOperation.constraints_hold env (to_flat_operations (op' :: ops')) := by
            rw [PreOperation.constraints_hold] at h_pre
            · exact h_pre
            · sorry
            · simp
            · simp
          have ih1 := ih h1
          simp [ih1]
        | Lookup l => sorry
        | Assign a => sorry


end Adversarial

@[simp]
def constraints_hold_from_list [Field F] : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => e.eval = 0
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval)
    | Operation.Circuit ⟨ soundness, _, _ ⟩ => soundness
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (e.eval = 0) ∧ constraints_hold_from_list ops
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval) ∧ constraints_hold_from_list ops
    | Operation.Circuit ⟨ soundness, _, _ ⟩ => soundness ∧ constraints_hold_from_list ops
    | _ => constraints_hold_from_list ops

/--
Weaker version of `constraints_hold_from_list` that captures the statement that, using the default
witness generator, checking all constraints would not fail.

For subcircuits, since we proved completeness, this only means we need to satisfy the assumptions!
-/
@[simp]
def passes_constraint_checks_from_list [Field F] : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => e.eval = 0
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval)
    | Operation.Circuit ⟨ _, completeness, _ ⟩ => completeness
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (e.eval = 0) ∧ passes_constraint_checks_from_list ops
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map Expression.eval) ∧ passes_constraint_checks_from_list ops
    | Operation.Circuit ⟨ _, completeness, _ ⟩ => completeness ∧ passes_constraint_checks_from_list ops
    | _ => passes_constraint_checks_from_list ops

@[simp]
def constraints_hold (circuit: Stateful F α) : Prop :=
  constraints_hold_from_list (circuit Context.empty).1.2

@[simp]
def passes_constraint_checks (circuit: Stateful F α) : Prop :=
  passes_constraint_checks_from_list (circuit Context.empty).1.2

@[reducible]
def output (circuit: Stateful F α) : α :=
  (circuit Context.empty).2

variable {α β γ: TypePair} [ProvableType F α] [ProvableType F β] [ProvableType F γ]
namespace Provable

private def witness' := witness (F:=F)

@[simp]
def witness {F: Type} [Field F] [ProvableType F α] (compute : Unit → α.value) :=
  let n := ProvableType.size F α
  let values : Vector F n := ProvableType.to_values (compute ())
  let varsM : Vector (Stateful F (Expression F)) n := values.map (fun v => witness' (fun () => v))
  do
    let vars ← varsM.mapM
    return ProvableType.from_vars vars

@[simp]
def assert_equal {F: Type} [Field F] [ProvableType F α] (a a': α.var) : Stateful F Unit :=
  let n := ProvableType.size F α
  let vars: Vector (Expression F) n := ProvableType.to_vars a
  let vars': Vector (Expression F) n := ProvableType.to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => assert_zero (x - x'))
  do let _ ← eqs.mapM

@[simp]
def assert_equal_silent {F: Type} [Field F] [ProvableType F α] (a a': α.var) : Stateful F Unit :=
  let n := ProvableType.size F α
  let vars: Vector (Expression F) n := ProvableType.to_vars a
  let vars': Vector (Expression F) n := ProvableType.to_vars a'
  let eqs := (vars.zip vars').map (fun ⟨ x, x' ⟩ => assert_zero_silent (x - x'))
  do let _ ← eqs.mapM
end Provable

-- goal: define circuit such that we can provably use it as subcircuit
structure FormalCircuit (F: Type) (β α γ: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β] [ProvableType F γ]
where
  -- β = inputs, α = outputs, γ = values of internal witnesses for "instrumenting" the circuit as prover
  main: β.var → (Option γ.value) → Stateful F α.var

  assumptions: β.value → Prop
  spec: β.value → α.value → Prop

  soundness:
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval F b_var = b → assumptions b →
    -- for all locally witnessed values
    ∀ c: γ.value,
    -- if the constraints hold
    constraints_hold (main b_var (some c)) →
    -- the the spec holds on the output
    let a := Provable.eval F (output (main b_var (some c)))
    spec b a

  completeness: open Provable in
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval F b_var = b → assumptions b →
    -- constraints hold when using the internal witness generator
    passes_constraint_checks (main b_var none)

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α γ) (b_var : β.var) (a_var : α.var) :=
  ∀ b : β.value,
    Provable.eval F b_var = b →
    circuit.assumptions b →
  ∀ a : α.value,
    Provable.eval F a_var = a
  → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α γ) (b_var : β.var) :=
  ∀ b : β.value,
    Provable.eval F b_var = b →
    circuit.assumptions b

def formal_circuit_to_subcircuit
  (circuit: FormalCircuit F β α γ) (b_var : β.var) (a_option : Option α.value) :
    (a_var: α.var) ×
    SubCircuit F
    (subcircuit_soundness circuit b_var a_var) (subcircuit_completeness circuit b_var) :=
  let main := circuit.main b_var none -- TODO

  -- modify `main` so that we optionally force the output variable to have a fixed value
  let main' := do
    let a ← main
    match a_option with
    | none => return a
    | some a_v => do
      let a' ← Provable.witness (fun () => a_v)
      Provable.assert_equal_silent a a' -- silent, because we don't want to "believe" this equation when proving soundness
      -- since we can't override the value of `a`, but a real prover can, we want to ignore its value
      return a'

  let res := main' Context.empty
  -- TODO: weirdly, when we destructure we can't deduce origin of the results anymore
  -- let ((_, ops), a_var) := res
  let ops := res.1.2
  let a_var := res.2

  let flat_ops := Adversarial.to_flat_operations ops
  let soundness := subcircuit_soundness circuit b_var a_var
  let completeness := subcircuit_completeness circuit b_var
  let input_size := ProvableType.size F β
  let output_size := ProvableType.size F α

  have s: SubCircuit F soundness completeness := by
    let b_vars: Vector (Expression F) input_size := ProvableType.to_vars b_var
    let assumptions (b: Vector F input_size) := circuit.assumptions (ProvableType.from_values b)
    let a_vars: Vector (Expression F) output_size := ProvableType.to_vars a_var

    use flat_ops, input_size, output_size, b_vars, assumptions, a_vars

    -- show imply_soundness
    intro b env h_eq_b as h_holds

    let a: α.value := Provable.eval_env env a_var
    intro b hb assumptions a' ha'

    suffices h: Adversarial.constraints_hold_from_list env ops from
      have ha : Provable.eval_env env (output main) = a := by
        dsimp [a, output, a_var, res]
        sorry
      -- circuit.soundness b b_var hb assumptions a ⟨ env, ⟨ h, ha ⟩ ⟩
      sorry

    guard_hyp h_holds : PreOperation.constraints_hold env (Adversarial.to_flat_operations ops)

    exact Adversarial.can_flatten_first env ops h_holds
    sorry

  ⟨ a_var, s ⟩

-- run a sub-circuit
@[simp]
def subcircuit (circuit: FormalCircuit F β α γ) (b: β.var) := as_stateful (F:=F) (
  fun _ =>
    let ⟨ a, subcircuit ⟩ := formal_circuit_to_subcircuit circuit b none
    let soundness := subcircuit_soundness circuit b a
    let completeness := subcircuit_completeness circuit b
    (Operation.Circuit ⟨ soundness, completeness, subcircuit ⟩, a)
)

@[simp]
def subcircuit_with_output (a_v: Option α.value) (circuit: FormalCircuit F β α γ) (b: β.var) := as_stateful (F:=F) (
  fun _ =>
    let ⟨ a, subcircuit ⟩ := formal_circuit_to_subcircuit (F:=F) circuit b a_v
    let soundness := subcircuit_soundness circuit b a
    let completeness := subcircuit_completeness circuit b
    (Operation.Circuit ⟨ soundness, completeness, subcircuit ⟩, a)
)
end Circuit


section -- examples
open Circuit
open Expression (const)

-- general Fp helpers
variable {p: ℕ} [Fact p.Prime]

def F p := ZMod p
instance isField : Field (F p) := ZMod.instField p
instance : CommRing (F p) := isField.toCommRing

def create (n: ℕ) (lt: n < p) : F p :=
  match p with
  | 0 => False.elim (Nat.not_lt_zero n lt)
  | _ + 1 => ⟨ n, lt ⟩

theorem create_eq {n: ℕ} {lt: n < p} (x : F p) (hx: x = create n lt) : x.val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rw [hx]; rfl

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
  row i := vec [from_byte i]

def ByteTable.soundness (x: F p) : ByteTable.contains (vec [x]) → x.val < 256 := by
  dsimp [Table.contains, ByteTable]
  rintro ⟨ i, h: vec [x] = vec [from_byte i] ⟩
  have h' : x = from_byte i := by repeat injection h with h
  have h'' : x.val = i.val := create_eq x h'
  rw [h'']
  exact i.is_lt

def byte_lookup (x: Expression (F p)) := lookup {
  table := ByteTable
  entry := vec [x]
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

open Provable (field field2 fields)

def add8 (x y: Expression (F p)) (z carry: Option (F p) := none) := do
  let z ← witness_or_value z (fun () => mod_256 (x + y))
  byte_lookup z
  let carry ← witness_or_value carry (fun () => floordiv (x + y) 256)
  assert_bool carry

  assert_zero (x + y - z - carry * (const 256))
  return z

def add8_full (input : Vector (Expression (F p)) 3) (locals: Option (Vector (F p) 2)) := do
  let ⟨ [x, y, carry_in], _ ⟩ := input
  -- TODO it's painful to destructure options like this, need a helper that does:
  -- Monad (Vector α n) -> Vector (Monad α) n
  let z := do let ⟨ [z, _], _ ⟩ ← locals; return z
  let carry_out := do let ⟨ [_, carry], _ ⟩ ← locals; return carry

  let z ← witness_or_value z (fun () => mod_256 (x + y + carry_in))
  byte_lookup z

  let carry_out ← witness_or_value carry_out (fun () => floordiv (x + y + carry_in) 256)
  assert_bool carry_out

  assert_zero (x + y + carry_in - z - carry_out * (const 256))
  return z

namespace Add8Full
def assumptions (input : Vector (F p) 3) :=
  let ⟨ [x, y, carry_in], _ ⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : Vector (F p) 3) (z: F p) :=
  let ⟨ [x, y, carry_in], _ ⟩ := input
  z.val = (x.val + y.val + carry_in.val) % 256

def circuit : FormalCircuit (F p) (fields (F p) 3) (field (F p)) (fields (F p) 2) where
  main := add8_full
  assumptions := assumptions
  spec := spec
  soundness := by
    -- introductions
    rintro ⟨ inputs, _ ⟩ ⟨ inputs_var, _ ⟩ h_inputs
    let [x, y, carry_in] := inputs
    let [x_var, y_var, carry_in_var] := inputs_var
    rintro as ⟨ witnesses, _ ⟩
    let [z, carry_out] := witnesses
    rintro h_holds z'

    -- characterize inputs
    have h_inputs' : [x_var.eval, y_var.eval, carry_in_var.eval] = [x, y, carry_in] := by injection h_inputs
    injection h_inputs' with hx h_inputs'
    injection h_inputs' with hy h_inputs'
    injection h_inputs' with hcarry_in

    -- characterize output, z' to equal (witness input) z, and replace in spec
    have hz : z' = z := rfl
    rw [hz]

    -- simplify constraints hypothesis
    dsimp at h_holds
    rw [hx, hy, hcarry_in] at h_holds
    let ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    -- simplify assumptions and spec
    dsimp [spec]
    dsimp [assumptions] at as

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)
    guard_hyp h_byte: ByteTable.contains (vec [z])
    guard_hyp h_bool_carry: carry_out * (carry_out + -1 * 1) = 0
    guard_hyp h_add: x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0

    show z.val = (x.val + y.val + carry_in.val) % 256

    -- reuse Boolean.equiv
    have h_bool_carry': carry_out = 0 ∨ carry_out = 1 := (Boolean.equiv carry_out).mp h_bool_carry
    -- reuse ByteTable.soundness
    have h_byte': z.val < 256 := ByteTable.soundness z h_byte
    sorry

  completeness := by
    -- introductions
    rintro ⟨ inputs, _ ⟩ ⟨ inputs_var, _ ⟩ h_inputs
    let [x, y, carry_in] := inputs
    let [x_var, y_var, carry_in_var] := inputs_var
    rintro as

    -- characterize inputs
    have h_inputs' : [x_var.eval, y_var.eval, carry_in_var.eval] = [x, y, carry_in] := by injection h_inputs
    injection h_inputs' with hx h_inputs'
    injection h_inputs' with hy h_inputs'
    injection h_inputs' with hcarry_in

    -- simplify assumptions
    dsimp [assumptions] at as

    -- unfold goal, (re)introduce names for some of unfolded variables
    dsimp
    rw [hx, hy, hcarry_in]
    let z := mod_256 (x + y + carry_in)
    let carry_out := floordiv (x + y + carry_in) 256
    rw [←(by rfl : z = mod_256 (x + y + carry_in))]
    rw [←(by rfl : carry_out = floordiv (x + y + carry_in) 256)]

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

    let goal_byte := ByteTable.contains (vec [z])
    let goal_bool := carry_out * (carry_out + -1 * 1) = 0
    let goal_add := x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add
    sorry
end Add8Full

def add8_wrapped (input : Vector (Expression (F p)) 2) (z: Option (F p)) := do
  let ⟨ [x, y], _ ⟩ := input
  let z ← subcircuit_with_output z Add8Full.circuit (vec [x, y, const 0])
  return z

namespace Add8
def spec (input : Vector (F p) 2) (z: F p) :=
  let ⟨ [x, y], _ ⟩ := input
  z.val = (x.val + y.val) % 256

def assumptions (input : Vector (F p) 2) :=
  let ⟨ [x, y], _ ⟩ := input
  x.val < 256 ∧ y.val < 256

def soundness_wrapped (inputs: Vector (F p) 2) (inputs_var: Vector (Expression (F p)) 2)
    (h_inputs: (Provable.eval (F p) (α:=(fields (F p) 2)) inputs_var) = inputs)
    (as: assumptions inputs)
    (z: (F p))
    (h: constraints_hold (add8_wrapped inputs_var (some z))) :
    let z' := Provable.eval (F p) (output (add8_wrapped inputs_var (some z)))
    spec inputs z'
  := by
  -- finish introductions
  let ⟨ [x, y], _ ⟩ := inputs
  let ⟨ [x_var, y_var], _ ⟩ := inputs_var
  intro z'

  -- characterize inputs
  have h_inputs' : [x_var.eval, y_var.eval] = [x, y] := by injection h_inputs
  injection h_inputs' with hx h_inputs'
  injection h_inputs' with hy

  -- characterize output, z' to equal (witness input) z, and replace in spec
  have hz : z' = z := by rfl
  rw [hz]

  -- simplify constraints hypothesis
  dsimp at h

  -- h is just `subcircuit_soundness` of `Add8Full.circuit`
  -- pass in the input values and a proof that they are correct
  have h_inputs'' : vec [x_var.eval, y_var.eval, 0] = vec [x, y, 0] := by rw [hx, hy]
  specialize h (vec [x, y, 0]) h_inputs''

  -- satisfy `Add8Full.assumptions` by using our own assumptions
  let ⟨ asx, asy ⟩ := as
  have as': Add8Full.assumptions (vec [x, y, 0]) := ⟨asx, asy, by tauto⟩
  specialize h as'

  -- pass in output value and a (trivial) proof that it's correct
  specialize h z hz
  guard_hyp h: Add8Full.circuit.spec (vec [x, y, 0]) z

  -- unfold `Add8Full` statements to show what the hypothesis is in our context
  dsimp [Add8Full.circuit, Add8Full.spec] at h
  guard_hyp h: z.val = (x.val + y.val + (0 : F p).val) % 256

  simp at h
  exact h

def circuit : FormalCircuit (F p) (fields (F p) 2) (field (F p)) (field (F p)) where
  main := add8_wrapped
  assumptions := assumptions
  spec := spec
  soundness := soundness_wrapped
  completeness := by
    -- introductions
    rintro ⟨ inputs, _ ⟩ ⟨ inputs_var, _ ⟩ h_inputs
    let [x, y] := inputs
    let [x_var, y_var] := inputs_var
    rintro as

    -- characterize inputs
    have h_inputs' : [x_var.eval, y_var.eval] = [x, y] := by injection h_inputs
    injection h_inputs' with hx h_inputs'
    injection h_inputs' with hy

    -- simplify assumptions
    dsimp [assumptions] at as

    -- simplify goal
    dsimp
    rw [hx, hy]

    -- the goal is just the `subcircuit_completeness` of `Add8Full.circuit`, i.e. show the assumptions hold
    -- introduce inputs and replace them with the eval'd variables in our context
    intro inputs' h_inputs'
    rw [←h_inputs']

    -- simplify `Add8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Add8Full.circuit, Add8Full.assumptions]
    show x.val < 256 ∧ y.val < 256 ∧ (0 = 0 ∨ 0 = 1)
    have ⟨ asx, asy ⟩ := as
    exact ⟨ asx, asy, by tauto ⟩

end Add8

def Main (x y : F p) : Stateful (F p) Unit := do
  -- in a real AIR definition, these could be inputs to every step
  let x ← create_input x 0
  let y ← create_input y 1

  let z ← add8 x y
  x.set_next y
  y.set_next z

#eval!
  let p := 1009
  let p_prime := Fact.mk prime_1009
  let p_non_zero := Fact.mk (by norm_num : p ≠ 0)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let main := do
    let x ← witness (fun _ => 10)
    let y ← witness (fun _ => 20)
    add8_wrapped (p:=p) (vec [x, y]) none
  let (ops, _) := main.run
  ops
end
