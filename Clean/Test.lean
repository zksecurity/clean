import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/--
  Example for using `structure ... : Prop` to define a list of properties that you can then use like a single `Prop`.
-/
structure Range (n a b: ℤ): Prop where
  lowerBound: a ≤ n
  upperBound: n < b

example (n: ℤ) : Range n 0 3 ∧ (n - 3)^2 = 1 → n = 2 := by
  rintro ⟨h1, h2⟩
  have h3 : n = 4 ∨ n = 2 := by
    have h4 : (n - 4)*(n - 2) = 0 := calc
      (n - 4)*(n - 2)
      _ = (n - 3)^2 - 1 := by ring
      _ = 1 - 1 := by rw [h2]
      _ = 0 := by ring
    cases (Int.eq_zero_or_eq_zero_of_mul_eq_zero h4)
    · left; linarith
    · right; linarith

  rcases h3 with (n4 | n2)
  · exfalso
    linarith [n4, h1.upperBound]
  · exact n2
