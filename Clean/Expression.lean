/-
  Expressions allow us to represent multivariate polynomials in a simple, computable way
  which is also suitable to be serialized to a file for the definition of an AIR.

  An expression, in our context, is a variable, a constant or a combination of those using
  addition and multiplication.

  Variables are indexed by a row and column index, which is a natural number.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

variable {F : Type} [Field F]

inductive Expression (F : Type) where
  | var : Nat -> Nat -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F
deriving Repr

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
def E (F: Type) [Field F] := Expression F

end Expression


-- examples of expressions

open Expression

def F2 := ZMod 2

deriving instance Field for F2

def BooleanCheck : E F2 := x * (1 - x)
def BooleanOr : E F2 := x + y - x * y

def Fibonacci1 : E F2 := y₀ - x₀ - x₁
def Fibonacci2 : E F2 := y₁ - y₀ - x₁

#eval Fibonacci1
