import Clean.Expression
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasLehmer

-- basic data defining an AIR
variable (ROWS COLUMNS N M : ℕ+)

def p := mersenne 31
def is_prime : p.Prime := lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)
instance : Fact p.Prime := Fact.mk is_prime

def F := ZMod p
instance : Field F := ZMod.instField p

/--
  A `Constraint` is a multivariate polynomial `C(X)` in the variables `X i j`, i = 0,...,ROWS-1 and j = 0,...,COLUMNS-1,
  along with a "local spec" which is any statement equivalent to `C X = 0`.

  The spec is intended to "describe" the constraint in a high-level way that can be easily composed to prove other specs.
-/
structure Constraint where
 poly : MultiPoly N M F
 spec : Inputs N M F -> Prop
 equiv : ∀ X, poly.eval X = 0 ↔ spec X

/-
  A few special cases that can be easily be cast to `Constraint`
-/
structure Constraint1 where
  expr : Expression F
  spec : F -> Prop
  equiv : ∀ x, expr.eval (Inputs.of1 x) = 0 ↔ spec x

structure Constraint2x1 where
  expr : Expression F
  spec : F -> F -> Prop
  equiv : ∀ x y, expr.eval (Inputs.of2x1 x y) = 0 ↔ spec x y

structure Constraint1x2 where
  expr : Expression F
  spec : TwoRows F -> Prop
  equiv : ∀ x₀ x₁, expr.eval (Inputs.of1x2 x₀ x₁) = 0 ↔ spec ⟨ x₀, x₁ ⟩

structure Constraint2x2 where
  poly : Expression F
  spec : TwoRows F -> TwoRows F -> Prop
  equiv : ∀ x₀ x₁ y₀ y₁, poly.eval (Inputs.of2x2 x₀ y₀ x₁ y₁) = 0 ↔ spec ⟨ x₀, x₁ ⟩ ⟨ y₀, y₁ ⟩

namespace Constraint

open Expression

def Boolean : Constraint1 := {
  expr := x * (1 - x)

  spec := fun x => x = 0 ∨ x = 1

  equiv := by
    intro x
    show x * (1 + (-1)*x) = 0 ↔ (x = 0 ∨ x = 1)
    simp
    constructor
    · rintro (_ | eq1)
      · tauto
      · right
        calc x
        _ = 1 - (1 + (-1)*x) := by ring
        _ = 1 := by simp [eq1]
    · rintro (_ | eq1)
      · tauto
      · right
        simp [eq1]
}

end Constraint

variable {ω : F}

-- the constraint_polynomial for constraint C(X_ij) is the function that maps witness polynomials P[0],...,P[M-1]
-- to the univariate polynomial
/- C(
  P[0](X), ..., P[M-1](X)
  P[0](ωX), ..., P[M-1](ωX)
  ...
  P[0](ω^{N-1}X), ..., P[M-1](ω^{N-1}X)
)
-/
def Constraint.polynomial (C : Constraint N M) : Polynomial F := sorry

-- An AIR is a constraint plus a vanishing polynomial which describes where the constraint holds
structure AIR where
  constraint : Constraint ROWS COLUMNS
  vanishing : Polynomial F

-- the "statement" of an AIR is that the vanishing polynomial divides the constraint
def AIR.Statement (a: AIR N M) :=
  let C := (Constraint.polynomial N M a.constraint)
  ∃ P : Polynomial F, C = a.vanishing * P
