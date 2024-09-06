import Clean.Expression
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasLehmer

-- basic data defining an AIR
variable (ROWS COLUMNS N M : ℕ+)

def p := mersenne 31
def is_prime : p.Prime := lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

def is_field : Field (ZMod p) := @ZMod.instField p (Fact.mk is_prime)

variable (F : Type) [Field F]

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
  expr : MultiPoly 1 1 F
  spec : F -> Prop
  equiv : ∀ x, expr.eval (Inputs.of1 x) = 0 ↔ spec x

structure Constraint1.out where
  poly : F
  spec : Prop
  equiv : poly = 0 ↔ spec

structure Constraint2 where
  poly : F -> F -> F
  spec : F -> F -> Prop
  equiv : ∀ x y, poly x y = 0 ↔ spec x y

structure Constraint1X2 where
  poly : TwoRows F -> F
  spec : TwoRows F -> Prop
  equiv : ∀ x, poly x = 0 ↔ spec x

structure Constraint2X2 where
  poly : TwoRows F -> TwoRows F -> F
  spec : TwoRows F -> TwoRows F -> Prop
  equiv : ∀ x y, poly x y = 0 ↔ spec x y

namespace Constraint

-- def define1 (f : F -> Constraint1.out F) : Constraint1 F := {
--   poly := fun x => (f x).poly,
--   spec := fun x => (f x).spec,
--   equiv := fun x => (f x).equiv
-- }
open Expression

def Boolean : Constraint1 F := {
  expr := ⟨ x * (1 - x) ⟩

  spec := fun x => x = 0 ∨ x = 1

  equiv := by
    intro x
    rw [Expression.x]
    -- TODO need more tools to unwrap definitions
    show x * (1 - x) = 0 ↔ (x = 0 ∨ x = 1)
    simp
    constructor
    · rintro (_ | eq1)
      · tauto
      · right
        calc x
        _ = 1 - (1 - x) := by ring
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
def Constraint.polynomial (C : Constraint N M F) : Polynomial F := sorry

-- An AIR is a constraint plus a vanishing polynomial which describes where the constraint holds
structure AIR where
  constraint : Constraint ROWS COLUMNS F
  vanishing : Polynomial F

-- the "statement" of an AIR is that the vanishing polynomial divides the constraint
def AIR.Statement (a: AIR N M F) :=
  let C := (Constraint.polynomial N M F a.constraint)
  ∃ P : Polynomial F, C = a.vanishing * P
