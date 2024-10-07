import Clean.Expression
import Clean.Gadgets.Boolean
import Clean.Gadgets.ByteLookup
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Addition32
open Expression

variable {p : ℕ} [Fact p.Prime]

-- Addition of elements from GL(2 ^ 32) as
-- x = x₀ + x₁ * 2 ^ 8 + x₂ * 2 ^ 16 + x₃ * 2 ^ 24 : ∀ i xi < 2 ^ 8


def lookup (N M : ℕ+) (x₀ x₁ x₂ x₃ : Expression (F p)) (n : ℕ+) : LookupArgument p N M :=
  {
    prop := fun env =>   (x₀.eval env).val < n
                       ∧ (x₁.eval env).val < n
                       ∧ (x₂.eval env).val < n
                       ∧ (x₃.eval env).val < n
  }

def AdditionConstraint (N M : ℕ+) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ z₀ z₁ z₂ z₃ c₀ c₁ c₂ c₃ : Expression (F p))
: GenericConstraint p N M :=
  GenericConstraint.mk
    [
      x₀ + y₀ - z₀ - c₀ * const (2 ^ 8),
      x₁ + y₁ + c₀ - z₁ - c₁ * const (2 ^ 8),
      x₂ + y₂ + c₁ - z₂ - c₂ * const (2 ^ 8),
      x₃ + y₃ + c₂ - z₃ - c₃ * const (2 ^ 8)
    ]

    [
      lookup N M x₀ x₁ x₂ x₃ (2 ^ 8),
      lookup N M y₀ y₁ y₂ y₃ (2 ^ 8),
      lookup N M z₀ z₁ z₂ z₃ (2 ^ 9),
    ]

    [
      Boolean.circuit N M c₀,
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
      have c₃ := c₃.eval env;
      (z.val = x.val + y.val % 2 ^ 32)
      ∧ c₃.val  = (x.val + y.val) / 2 ^ 32
    )

-- def Num32 := { x : F p × F p × F p × F p
--                //  x.1.val < 2 ^ 8 ∧ x.2.1.val < 2 ^ 8
--                    ∧ x.2.1.val < 2 ^ 8 ∧ x.2.1.val < 2 ^ 8 }

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

    set x₀ := x₀.eval X
    set x₁ := x₁.eval X
    set x₂ := x₂.eval X
    set x₃ := x₃.eval X

    set y₀ := y₀.eval X
    set y₁ := y₁.eval X
    set y₂ := y₂.eval X
    set y₃ := y₃.eval X

    set z₀ := z₀.eval X
    set z₁ := z₁.eval X
    set z₂ := z₂.eval X
    set z₃ := z₃.eval X

    set c₀ := c₀.eval X
    set c₁ := c₁.eval X
    set c₂ := c₂.eval X
    set c₃ := c₃.eval X

    intro h₁ h₂ h₃
    simp [eval]
    constructor
    . intro h
      rcases (And.right h) with
      --⟨hxyz1, hxyz2, hxyz3, hzc0 | hoc0, hzc1 | hozc1, hzc2 | hozc2, hzc3 | hozc3⟩
      ⟨hxyz1, hxyz2, hxyz3, hc0, hc1, hc2, hc3⟩
      sorry

    . sorry
