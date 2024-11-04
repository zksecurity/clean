import Clean.Utils.Field
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-
  Formalization of the theorems from
  [1] U. Haböck, "Multivariate lookups based on logarithmic derivatives"
      https://eprint.iacr.org/2022/1530
-/
section LogUp

variable (p : ℕ) [Fact p.Prime]
open Polynomial

lemma prod_fin_succ {β : Type} [CommRing β] (n : ℕ) (f : Fin (n + 1) -> β) :
    (∏ i, f i) = f n * (∏ i : Fin n, f i) := by
  induction' n with n ih
  · simp
  · simp
    specialize ih (λ i => f (Fin.castSucc i)); simp at ih
    have fin_eq_range_succ: ∏ i ∈ Finset.range (n.succ.succ), f i = ∏ i : Fin (n.succ.succ), f i := by
      rw [Finset.prod_range (λ x : ℕ => f _)]
      simp
    have fin_eq_range: ∏ i ∈ Finset.range (n.succ), f i = ∏ i : Fin (n.succ), f i := by
      rw [Finset.prod_range (λ x : ℕ => f _)]
    rw [←fin_eq_range_succ, Finset.prod_range_succ, mul_comm, fin_eq_range]
    simp

lemma sum_fin_succ {β : Type} [CommRing β] (n : ℕ) (f : Fin (n + 1) -> β) :
    (∑ i, f i) = f n + (∑ i : Fin n, f i) := by
  induction' n with n ih
  · simp
  · simp
    specialize ih (λ i => f (Fin.castSucc i)); simp at ih
    have fin_eq_range_succ: ∑ i ∈ Finset.range (n.succ.succ), f i = ∑ i : Fin (n.succ.succ), f i := by
      rw [Finset.sum_range (λ x : ℕ => f _)]; simp
    have fin_eq_range: ∑ i ∈ Finset.range (n.succ), f i = ∑ i : Fin (n.succ), f i := by
      rw [Finset.sum_range (λ x : ℕ => f _)]
    rw [←fin_eq_range_succ, Finset.sum_range_succ, add_comm]
    simp [fin_eq_range]

lemma prod_leadingCoefficient_neq_zero (n : ℕ) (S : (Fin n) -> (F p)) :
    (∏ i : Fin n, (X - C (S i))).leadingCoeff ≠ 0 := by
  induction' n with n ih
  · simp
  · rw [prod_fin_succ, Polynomial.leadingCoeff_mul]; simp
    specialize ih (λ i => S (Fin.castSucc i))
    rw [←Polynomial.leadingCoeff_eq_zero]; assumption


lemma prod_leadingCoefficient_eq_one (n : ℕ) (S : (Fin n) -> (F p)) :
    (∏ i : Fin n, (X - C (S i))).leadingCoeff = 1 := by
  induction' n with n ih
  · simp
  · rw [prod_fin_succ, Polynomial.leadingCoeff_mul]; simp
    apply ih

lemma prod_neq_zero (n : ℕ) (S : (Fin n) -> (F p)) :
    (∏ i : Fin n, (X - C (S i))) ≠ 0 := by
  simp
  rw [←Polynomial.leadingCoeff_eq_zero]
  exact prod_leadingCoefficient_neq_zero p n S

lemma monomial_neq_zero (a : F p) : (X - C a) ≠ 0 := by
  have thm := prod_neq_zero p 1 (λ _ : Fin 1 => a)
  simp at thm; exact thm

lemma prod_degree (n : ℕ) (S : (Fin n) -> (F p)) :
    (∏ i : Fin n, (X - C (S i))).natDegree = n := by
  induction' n with n ih
  · simp
  · simp [prod_fin_succ]
    rw [Polynomial.natDegree_mul']
    · rw [sub_eq_add_neg, ←Polynomial.C_neg, Polynomial.natDegree_X_add_C, ih]; ring
    · rw [Polynomial.leadingCoeff_X_sub_C]
      specialize ih (λ i => S (Fin.castSucc i))
      simp; apply prod_neq_zero

lemma prod_eq_algebramap (N : ℕ) (S : (Fin N) -> (F p)) :
    ∏ x : Fin N, ((algebraMap (F p)[X] (RatFunc (F p))) X - (algebraMap (F p)[X] (RatFunc (F p))) (C (S x)))
    =
    algebraMap (F p)[X] (RatFunc (F p)) (∏ i : Fin N, (X - C (S i))) := by
  simp

theorem derivative_zero_constant (g : (F p)[X]) (h_deg : g.natDegree < p) :
    derivative g = 0 → ∃ a : F p, g = C a := by
  intro h
  simp [derivative, Polynomial.sum] at h
  sorry

/--
  Definition of derivative for rational functions
  Equation (5) of [1]
-/
noncomputable def ratFuncDderivative (q : RatFunc (F p)) : RatFunc (F p) :=
  RatFunc.liftOn' q (λ x y => RatFunc.mk (derivative x * y - y * derivative x) (y^2))
    (by
    intros g q c hq hc
    simp
    -- TODO: we need to prove that this definition is well-defined
    sorry)

/--
  Lemma 2 of [1]
-/
theorem derivative_ratfunc_zero_constant (g q : (F p)[X]) (g_deg : g.natDegree < p) (q_deg : q.natDegree < p) :
    ratFuncDderivative p (RatFunc.mk g q) = 0 → ∃ a : F p, (RatFunc.mk g q) = ↑(C a) := by
  sorry

/--
  Follow up to lemma 2, if the leading coefficient of the numerator and the denominator
  are both 1 and the rational function is some constant, then the numerator and the denominator
  are equal
-/
theorem ratfunc_constant_leading_coeff
    (g q : (F p)[X])
    (g_deg : g.natDegree < p) (q_deg : q.natDegree < p)
    (leading_g : g.leadingCoeff = 1) (leading_q : q.leadingCoeff = 1)
    (h : ∃ a : F p, (RatFunc.mk g q) = ↑(C a)) : g = q := by
  sorry

/--
  The logarithmic derivative of a polynomial g is defined as
  the following rational function: the formal derivative of g divided by g
  Section 2.3 of [1]
-/
noncomputable def logDerivative {β : Type} [CommRing β] [IsDomain β] (g : β[X]) : RatFunc β :=
  RatFunc.mk (derivative g) g

/--
  The logarithmic derivative of a product of two polynomials is equal to the sum of the
  logarithmic derivatives of the two polynomials
  section 2.3 of [1]
-/
theorem log_derivative_prod (g h : (F p)[X])
    (g_neq_zero : g ≠ 0) (h_neq_zero : h ≠ 0) :
    logDerivative (g * h) = logDerivative g + logDerivative h := by
  simp [logDerivative, Polynomial.derivative_add]
  rw [add_div, mul_div_mul_right, mul_div_mul_left]
  repeat simp; assumption

/--
  The logarithmic derivative of a polynomial of the form (∏ i : Fin N, (X - C (A i)))
  is equal to the sum ∑ i : Fin N, 1 / (X - C (A i))
  Section 2.3, equation (7) of [1]
-/
theorem log_derivative_prod_roots (N : ℕ) (A : Fin N -> F p) :
    logDerivative (∏ i : Fin N, (X - C (A i))) = ∑ i : Fin N, RatFunc.mk 1 (X - C (A i)) := by
  induction' N with N ih
  · simp [logDerivative]
  · simp [prod_fin_succ]
    rw [log_derivative_prod, ih, logDerivative, Polynomial.derivative, sum_fin_succ]; simp
    apply monomial_neq_zero; apply prod_neq_zero

/--
  Permutation argument over log derivatives
  Lemma 3 of [1]
-/
theorem logup_permutation (N : ℕ) (field_assumption: p > N) (A B : Fin N -> F p) :
    (∏ i : Fin N, (X - C (A i)) = ∏ i : Fin N, (X - C (B i)))
    ↔
    (∑ i : Fin N, RatFunc.mk 1 (X - C (A i)) = ∑ i : Fin N, RatFunc.mk 1 (X - C (B i))) := by
  constructor
  · -- as stated in the paper, trivially if the products are equal, then
    -- their log derivatives coincide
    intro h
    apply_fun logDerivative at h
    rw [log_derivative_prod_roots, log_derivative_prod_roots] at h; exact h
  · intro h
    set pa := ∏ i : Fin N, (X - C (A i))
    set pb := ∏ i : Fin N, (X - C (B i))

    have lem1 (S : Fin N -> F p) :
      logDerivative (∏ i : Fin N, (X - C (S i))) = ∑ i : Fin N, RatFunc.mk 1 (X - C (S i)) := by
      rw [←log_derivative_prod_roots]

    rw [←lem1, ←lem1] at h
    unfold logDerivative at h
    simp at h

    have lem2 (S : Fin N -> F p) :
        ∏ x : Fin N, ((algebraMap (F p)[X] (RatFunc (F p))) X - (algebraMap (F p)[X] (RatFunc (F p))) (C (S x))) ≠ 0 := by
      rw [prod_eq_algebramap, Ne, RatFunc.algebraMap_eq_zero_iff]
      apply prod_neq_zero

    rw [div_eq_iff (lem2 A), mul_comm, ←mul_div_assoc, eq_div_iff (lem2 B)] at h

    have lem3 : ratFuncDderivative p (RatFunc.mk pa pb) = 0 := by
      simp only [ratFuncDderivative]
      rw [RatFunc.liftOn'_mk]
      · -- here we need to actually prove that the log derivative is zero
        sorry
      · simp

    have p_deg (S : Fin N -> F p) : (∏ i : Fin N, (X - C (S i))).natDegree < p := by
      rw [prod_degree p N S]
      exact field_assumption

    have lem4 := derivative_ratfunc_zero_constant p pa pb (p_deg A) (p_deg B) lem3
    apply ratfunc_constant_leading_coeff p pa pb
      (p_deg A) (p_deg B)
      (prod_leadingCoefficient_eq_one p N A) (prod_leadingCoefficient_eq_one p N B) lem4

/--
  Uniqueness of the fractional decomposition
  Lemma 4 of [1]
-/
theorem fractional_decomposition_unique {β : Type} [Field β] [Fintype β] (m₁ m₂ : β -> β) :
    (∑ z : β, RatFunc.mk (C (m₁ z)) (X - C z) = ∑ z : β, RatFunc.mk (C (m₂ z)) (X - C z))
    ↔
    ∀ z : β, m₁ z = m₂ z := by
  sorry

/--
  Set inclusion
  Lemma 5 of [1]
-/
theorem logup_set_inclusion (N : ℕ) (field_assumption: p > N) (A B : Fin N -> F p):
    (∀ i, ∃ j, A i = B j)
    ↔
    (
      ∃ m : Fin N -> F p,
      (∑ i : Fin N, RatFunc.mk 1 (X - C (A i)) = ∑ i : Fin N, RatFunc.mk (C (m i)) (X - C (B i)))
    ) := by
  sorry

end LogUp
