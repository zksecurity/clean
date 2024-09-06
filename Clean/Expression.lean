/-
  Expressions allow us to represent multivariate polynomials in a simple, computable way
  which is also suitable to be serialized to a file for the definition of an AIR.

  An expression, in our context, is a variable, a constant or a combination of those using
  addition and multiplication.

  Variables are indexed by a row and column index, which is a natural number.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

variable {F : Type} [CommRing F]

inductive Expression (F : Type) where
  | var : Nat -> Nat -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
deriving Repr -- TODO more efficient string representation

namespace Expression
open Expression

-- a few variables to work with

def x : Expression F := var 0 0
def y : Expression F := var 0 1
def z : Expression F := var 0 2

structure TwoRows (F : Type) where
  this : Expression F
  next : Expression F

def x₀ : Expression F := var 0 0
def x₁ : Expression F := var 1 0
def X : TwoRows F := ⟨ x₀, x₁ ⟩

def y₀ : Expression F := var 0 1
def y₁ : Expression F := var 1 1
def Y : TwoRows F := ⟨ y₀, y₁ ⟩

def z₀ : Expression F := var 0 2
def z₁ : Expression F := var 1 2
def Z : TwoRows F := ⟨ z₀, z₁ ⟩

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

instance : HMul F (Expression F) (Expression F) where
  hMul := fun f e => mul f e

def zero : Expression F := 0
def one : Expression F := 1
def E (F: Type) [CommRing F] := Expression F

-- evaluate an expression

def eval (env : Nat -> Nat -> F) : Expression F -> F
  | var i j => env i j
  | const f => f
  | add e₁ e₂ => eval env e₁ + eval env e₂
  | mul e₁ e₂ => eval env e₁ * eval env e₂

end Expression

-- define a multivariate polynomial over a CommRing as an expression
-- with an eval function on a _finite_ matrix of variables (cycling through the matrix if necessary)
variable {N M : ℕ+}

structure MultiPoly (N M : ℕ+) (F : Type) [CommRing F] where
  expr : Expression F
deriving Repr

def MultiPoly.eval (P: MultiPoly N M F) (X : Fin N -> Fin M -> F) : F :=
  P.expr.eval (fun i j => X (Fin.ofNat' i N.prop) (Fin.ofNat' j M.prop))

-- examples of expressions

open Expression

def F2 := ZMod 2
deriving instance CommRing for F2

def BooleanCheck : E F2 := x * (1 - x)
def BooleanOr : E F2 := x + y - x * y

#check MultiPoly.mk

def FibonacciInitX : MultiPoly 2 2 ℚ := ⟨ X.this - 1 ⟩
def FibonacciInitY : MultiPoly 2 2 ℚ := ⟨ Y.this - 1 ⟩
def Fibonacci1 : MultiPoly 2 2 ℚ := ⟨ X.next - X.this - Y.this ⟩
def Fibonacci2 : MultiPoly 2 2 ℚ := ⟨ Y.next - X.next - Y.this ⟩

#eval BooleanCheck
#eval Fibonacci1

def X : Nat -> Nat -> F2
  | 0, 0 => 1
  | 0, 1 => 0
  | _, _ => 0

example : eval X x = 1 := rfl
example : eval X y = 0 := rfl
example : eval X (x + y) = 1 := rfl
example : eval X BooleanOr = 1 := rfl

def Fib : (Fin 2) -> (Fin 2) -> ℚ
  | 0, 0 => 1
  | 0, 1 => 1
  | 1, 0 => 2
  | 1, 1 => 3

#eval FibonacciInitX.eval Fib
#eval FibonacciInitY.eval Fib
#eval Fibonacci1.eval Fib
#eval Fibonacci2.eval Fib
