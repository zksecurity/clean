/-
  Expressions allow us to represent multivariate polynomials in a simple, computable way
  which is also suitable to be serialized to a file for the definition of an AIR.

  An expression, in our context, is a variable, a constant or a combination of those using
  addition and multiplication.

  Variables are indexed by a row and column index.
  The row index is a ZMod M because we want to support indexing the next row, possibly wrapping around.
  The column index is a Fin N because the colum index is bounded, and it does not make sense to
  do operations between column indices.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic


inductive Expression (N : ℕ+) (M : ℕ) (F : Type) where
  | var : Fin M -> Fin N -> Expression N M F
  | const : F -> Expression N M F
  | add : Expression N M F -> Expression N M F -> Expression N M F
  | mul : Expression N M F -> Expression N M F -> Expression N M F
deriving Repr -- TODO more efficient string representation

/--
  A Row is a mapping from the column inde to a value in the field F.
-/
def Row (M : ℕ+) (F: Type) := Fin M -> F

/--
  A trace is an inductive list of rows.
-/
inductive Trace (N : ℕ+) (F : Type) :=
  /-- An empty trace -/
  | empty : Trace N F
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace N F) (row: Row N F) : Trace N F

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

/--
  The length of a trace is the number of rows it contains.
-/
def Trace.len {N : ℕ+} {F : Type} : Trace N F -> ℕ
  | <+> => 0
  | rest +> _ => Nat.succ rest.len

def Trace.everyRowTwoRowsInduction {M : ℕ+} {F : Type} {P : Trace M F → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row M F, P (empty +> row))
    (more : ∀ curr next : Row M F, ∀ rest : Trace M F, P (rest) -> P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

/--
  A trace of length M is a trace with exactly M rows.
-/
def TraceOfLength (N : ℕ+) (M : ℕ) (F : Type)  : Type := { env : Trace N F // env.len = M }

def Trace.getLe {N: ℕ+} {F : Type} : (env : Trace N F) -> (row : Fin env.len) -> (j : Fin N) -> F
  | _ +> currRow, ⟨0, _⟩, columnIndex => currRow columnIndex
  | rest +> _, ⟨Nat.succ i, h⟩, j => getLe rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

def TraceOfLength.get {N: ℕ+} {M : ℕ} {F : Type} : (env : TraceOfLength N M F) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLe (by rw [←h] at i; exact i) j

/--
  Evaluation function of an expression over a trace.
-/
def TraceOfLength.eval {N: ℕ+} {M : ℕ} {F : Type} [CommRing F] : (env : TraceOfLength N M F) -> Expression N M F -> F
  | env, Expression.var i j => env.get i j
  | _, Expression.const f => f
  | env, Expression.add e₁ e₂ => env.eval e₁ + env.eval e₂
  | env, Expression.mul e₁ e₂ => eval env e₁ * eval env e₂

namespace Expression
variable {N : ℕ+} {M : ℕ} {F : Type} [CommRing F]

-- combine expressions elegantly
instance : Zero (Expression N M F) where
  zero := const 0

instance : One (Expression N M F) where
  one := const 1

instance : Add (Expression N M F) where
  add := add

instance : Neg (Expression N M F) where
  neg e := mul (const (-1)) e

instance : Sub (Expression N M F) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (Expression N M F) where
  mul := mul

instance : Coe F (Expression N M F) where
  coe f := const f

instance : HMul F (Expression N M F) (Expression N M F) where
  hMul := fun f e => mul f e

def zero : Expression N M F := 0
def one : Expression N M F := 1
def E (F: Type) [CommRing F] := Expression N M F


-- evaluate an expression over a trace
def eval (env : Trace N F) : Expression N env.len F -> F
  | var i j => env.getLe i j
  | const f => f
  | add e₁ e₂ => eval env e₁ + eval env e₂
  | mul e₁ e₂ => eval env e₁ * eval env e₂

end Expression

structure MultiPoly (N M : ℕ+) (F : Type) [CommRing F] where
  expr : Expression N M F
--deriving Repr

-- namespace MultiPoly
-- -- define a multivariate polynomial as an
-- -- expression with a _fixed number of input variables_
-- variable {N M : ℕ+}
-- variable {F : Type} [CommRing F]

-- def eval (P: MultiPoly N M F) (env : Inputs N M F) : F := P.expr.eval env

-- end MultiPoly



/-
-- simpler inputs for specific variable layouts
namespace Inputs

def of1 {F : Type} (f : F) : Inputs 1 1 F := fun _ _ => f

def of1x2 {F : Type} (f₀ f₁ : F) : Inputs 1 2 F
  | 0, Fin 0 => f₀
  | 0, Fin 1 => f₁

def of2x1 {F : Type} (f₀ f₁ : F) : Inputs 2 1 F
  | 0, 0 => f₀
  | 1, 0 => f₁

def of2x2 {F : Type} (f₀₀ f₀₁ f₁₀ f₁₁ : F) : Inputs 2 2 F :=
  fun i j => match i, j with
    | 0, 0 => f₀₀
    | 0, 1 => f₀₁
    | 1, 0 => f₁₀
    | 1, 1 => f₁₁

end Inputs

-- not sure if we need this

-- namespace Expression

-- def eval1 (x : F) : Expression F -> F
--   | var _ _ => x
--   | const f => f
--   | add e₁ e₂ => eval1 x e₁ + eval1 x e₂
--   | mul e₁ e₂ => eval1 x e₁ * eval1 x e₂

-- theorem eval1_equiv (expr: Expression F) : ∀ x, expr.eval (Inputs.of1 x) = expr.eval1 x :=
--   by
--     intro x
--     induction expr with
--     | var i j => rfl
--     | const f => rfl
--     | add e₁ e₂ ih₁ ih₂ => simp [eval, eval1, ih₁, ih₂]
--     | mul e₁ e₂ ih₁ ih₂ => simp [eval, eval1, ih₁, ih₂]

-- end Expression

-- examples of expressions

section
open Expression
open MultiPoly

def F2 := ZMod 2
deriving instance CommRing for F2

def BooleanCheck : E F2 := x * (1 - x)
def BooleanOr : E F2 := x + y - x * y

def FibonacciInitX : MultiPoly 2 2 ℚ := ⟨ X.this - 1 ⟩
def FibonacciInitY : MultiPoly 2 2 ℚ := ⟨ Y.this - 1 ⟩
def Fibonacci1 : MultiPoly 2 2 ℚ := ⟨ X.next - X.this - Y.this ⟩
def Fibonacci2 : MultiPoly 2 2 ℚ := ⟨ Y.next - X.next - Y.this ⟩

#eval BooleanCheck
#eval Fibonacci1

def Bools : Inputs 1 2 F2
  | 0, 0 => 1
  | 0, 1 => 0

example : x.eval Bools = 1 := rfl
example : y.eval Bools = 0 := rfl
example : (x + y).eval Bools  = 1 := rfl
example : BooleanOr.eval Bools = 1 := rfl

def Fib : Inputs 2 2 ℚ
  | 0, 0 => 1
  | 0, 1 => 1
  | 1, 0 => 2
  | 1, 1 => 3

#eval FibonacciInitX.eval Fib
#eval FibonacciInitY.eval Fib
#eval Fibonacci1.eval Fib
#eval Fibonacci2.eval Fib

end

-/
