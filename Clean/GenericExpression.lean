/-
  GenericExpressions allow us to represent multivariate polynomials in a simple, computable way
  which is also suitable to be serialized to a file for the definition of an AIR.

  Variables are indexed by a natural number.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic



variable {F : Type} [CommRing F] [Fintype F]

inductive GenericExpression (F : Type) where
  | var : Nat -> GenericExpression F
  | const : F -> GenericExpression F
  | add : GenericExpression F -> GenericExpression F -> GenericExpression F
  | mul : GenericExpression F -> GenericExpression F -> GenericExpression F
deriving Repr

namespace GenericExpression
open GenericExpression

-- combine expressions elegantly

instance : Zero (GenericExpression F) where
  zero := const 0

instance : One (GenericExpression F) where
  one := const 1

instance : Add (GenericExpression F) where
  add := add

instance : Neg (GenericExpression F) where
  neg e := mul (const (-1)) e

instance : Sub (GenericExpression F) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (GenericExpression F) where
  mul := mul

instance : Coe F (GenericExpression F) where
  coe f := const f

instance : HMul F (GenericExpression F) (GenericExpression F) where
  hMul := fun f e => mul f e

def zero : GenericExpression F := 0
def one : GenericExpression F := 1
def E (F: Type) [CommRing F] := GenericExpression F -- evaluate an expression

def eval (env : Nat -> F) : GenericExpression F -> F
  | var i => env i
  | const f => f
  | add e₁ e₂ => eval env e₁ + eval env e₂
  | mul e₁ e₂ => eval env e₁ * eval env e₂


def instantiate (env : Nat -> GenericExpression F) : GenericExpression F -> GenericExpression F
  | var i => env i
  | const f => const f
  | add e₁ e₂ => add (instantiate env e₁) (instantiate env e₂)
  | mul e₁ e₂ => mul (instantiate env e₁) (instantiate env e₂)

end GenericExpression


def GenericInputs (F : Type) := (Nat) → F
