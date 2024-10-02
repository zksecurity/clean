import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Addition32
open Expression

variable {p : ℕ} [Fact p.Prime]

-- Addition of elements from GL(2 ^ 32) as
-- x = x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃ * 2 ^ 24

def lookup (N M : ℕ+) (x₀ x₁ x₂ x₃ : Expression (F p)) : LookupArgument p N M :=
  {
    prop := fun env =>   (x₀.eval env).val < 2 ^ 8
                       ∧ (x₁.eval env).val < 2 ^ 8
                       ∧ (x₂.eval env).val < 2 ^ 8
                       ∧ (x₃.eval env).val < 2 ^ 8
  }

def AdditionConstraint (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
: GenericConstraint p N M :=
  GenericConstraint.mk
    [ x₀ + y₀ - z₀ - c₀ * const (2 ^ 8),
      x₁ + y₁ - z₁ - c₁ * const (2 ^ 8),
      x₂ + y₂ - z₂ - c₂ * const (2 ^ 8),
      x₃ + y₃ - z₃ - c₃ * const (2 ^ 8)
    ]

    [ lookup N M x₀ x₁ x₂ x₃,
      lookup N M y₀ y₁ y₂ y₃,
      lookup N M z₀ z₁ z₂ z₃,
    ]

    [ Boolean.circuit N M c₀,
      Boolean.circuit N M c₁,
      Boolean.circuit N M c₂,
      Boolean.circuit N M c₃
    ]

def spec (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
  : Inputs N M (F p) -> Prop :=
    (fun env =>
      have x := (x₀.eval env) + (x₁.eval env) * 2 ^ 8 + (x₂.eval env) * 2 ^ 16 + (x₃.eval env) * 2 ^ 24;
      have y := (y₀.eval env) + (y₁.eval env) * 2 ^ 8 + (y₂.eval env) * 2 ^ 16 + (y₃.eval env) * 2 ^ 24;
      have z := (z₀.eval env) + (z₁.eval env) * 2 ^ 8 + (z₂.eval env) * 2 ^ 16 + (z₃.eval env) * 2 ^ 24;
      have c₀ := c₀.eval env;
      have c₁ := c₁.eval env;
      have c₂ := c₂.eval env;
      have c₃ := c₃.eval env;
      (z.val = x.val + y.val % 2 ^ 32)
      ∧ c₀.val + c₁.val + c₂.val + c₃.val  = (x.val + y.val) / 2 ^ 32
    )


theorem equiv (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p)) :
  (∀ X,
    (forallList
         (fullLookupSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
         (fun lookup => lookup.prop X))
    -> (
      (forallList
         (fullConstraintSet (AdditionConstraint N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃))
         (fun constraint => constraint.eval X = 0))
      ↔
      spec N M x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ X
    )
  ) := by
    intro X
    simp [forallList, ByteLookup.lookup]
    let equivBoolean0 := Boolean.equiv N M c₀ X
    let equivBoolean1 := Boolean.equiv N M c₁ X
    let equivBoolean2 := Boolean.equiv N M c₂ X
    let equivBoolean3 := Boolean.equiv N M c₃ X
    simp [forallList, Boolean.spec] at equivBoolean0
    simp [forallList, Boolean.spec] at equivBoolean1
    simp [forallList, Boolean.spec] at equivBoolean2
    simp [forallList, Boolean.spec] at equivBoolean3
    rw [equivBoolean0, equivBoolean1, equivBoolean2, equivBoolean3, spec]
    intro h₁ h₂ h₃
    simp [eval]
    constructor
    . sorry
    . sorry
