/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# Comparing the two reciprocal charts of an apolar locator

The outer polynomial variable is the one in which we divide by the locator.
Its coefficients are polynomials in the other coordinate. Their reversals
clear the denominators caused by passing to the inverse coordinate.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts

open Polynomial
variable {K : Type*} [Field K]
local notation "Biv" => Polynomial (Polynomial K)

/-- Reverse all coefficient polynomials to a common degree for comparison of charts. -/
noncomputable def reverseCoeffs (m : ℕ) (A : Biv) : Biv :=
  ⟨.ofCoeff (A.coeff.mapRange (reflect m) reflect_zero)⟩

@[simp] theorem coeff_reverseCoeffs (m : ℕ) (A : Biv) (j : ℕ) :
    (reverseCoeffs m A).coeff j = reflect m (A.coeff j) := rfl

private theorem rev_outer (m : ℕ) (A : Biv) : (reverseCoeffs m A).natDegree ≤ A.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp [coeff_eq_zero_of_natDegree_lt hj]

private theorem equal_below_locator {f A B : Biv} (ha : A.natDegree < f.natDegree)
    (hb : B.natDegree < f.natDegree) (h : f ∣ A-B) : A=B := by
  by_contra hn
  have h0 := sub_ne_zero.mpr hn
  obtain ⟨v,hv⟩ := h
  have hfv : f ≠ 0 ∧ v ≠ 0 := mul_ne_zero_iff.mp (hv ▸ h0)
  have low := (natDegree_sub_le A B).trans_lt (max_lt ha hb)
  rw [hv,natDegree_mul hfv.1 hfv.2] at low
  omega

private theorem scaled_below {A f : Biv} (h : A.natDegree < f.natDegree) (c : Polynomial K) :
    (C c * A).natDegree < f.natDegree := (natDegree_C_mul_le _ _).trans_lt h

/-- Below the locator degree a chart congruence gives literal equalities of coefficients. -/
theorem compare_coefficients {m : ℕ} {A B f : Biv} {u v : Polynomial K}
    (ha : A.natDegree < f.natDegree) (hb : B.natDegree < f.natDegree)
    (hc : f ∣ C u * reverseCoeffs m B - C v * A) (j : ℕ) :
    u * reflect m (B.coeff j) = v * A.coeff j := by
  have eq := equal_below_locator (scaled_below ((rev_outer m B).trans_lt hb) u)
    (scaled_below ha v) hc
  simpa only [coeff_C_mul,coeff_reverseCoeffs] using congrArg (fun P : Biv => P.coeff j) eq

/-- The coordinate degree of the quotient after comparison at reciprocal coordinates. -/
theorem chart_degree {m b : ℕ} {A B f : Biv} (ha : A.natDegree < f.natDegree)
    (hb : B.natDegree < f.natDegree) (hm : ∀ j, (B.coeff j).natDegree ≤ m)
    (hc : f ∣ C (X^b) * reverseCoeffs m B - C (X^m) * A) (j : ℕ) :
    (A.coeff j).natDegree ≤ b := by
  by_cases hz : A.coeff j = 0
  · simp [hz]
  have eq := compare_coefficients ha hb hc j
  have hr := (natDegree_reflect_le (N := m) (p := B.coeff j)).trans (max_le le_rfl (hm j))
  have hdeg : ((X^b : Polynomial K) * reflect m (B.coeff j)).natDegree ≤
      (X^b : Polynomial K).natDegree + (reflect m (B.coeff j)).natDegree := natDegree_mul_le
  rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) hz, natDegree_X_pow, natDegree_X_pow] at hdeg
  omega

/-- A positive gap between the reciprocal powers forces both chart remainders to vanish. -/
theorem negative_twist {m k : ℕ} (hk : 0 < k) {A B f : Biv}
    (ha : A.natDegree < f.natDegree) (hb : B.natDegree < f.natDegree)
    (hm : ∀ j, (B.coeff j).natDegree ≤ m)
    (hc : f ∣ C 1 * reverseCoeffs m B - C (X^(m+k)) * A) : A=0 ∧ B=0 := by
  have hzero (j : ℕ) : A.coeff j = 0 := by
    by_contra hz
    have eq := compare_coefficients ha hb hc j
    rw [one_mul] at eq
    have hr := (natDegree_reflect_le (N := m) (p := B.coeff j)).trans (max_le le_rfl (hm j))
    rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) hz,natDegree_X_pow] at hr
    omega
  refine ⟨Polynomial.ext fun j => by simp [hzero], Polynomial.ext fun j => ?_⟩
  have eq := compare_coefficients ha hb hc j
  simpa [hzero] using eq

/-- At zero twist the remaining quotient is an actual polynomial in the outer variable,
with no dependence on the chart parameter. -/
theorem zero_twist {m : ℕ} {A B f : Biv}
    (ha : A.natDegree < f.natDegree) (hb : B.natDegree < f.natDegree)
    (hm : ∀ j, (B.coeff j).natDegree ≤ m)
    (hc : f ∣ C 1 * reverseCoeffs m B - C (X^m) * A) :
    ∃ P : Polynomial K, A = P.map C := by
  refine ⟨A.map (evalRingHom 0), Polynomial.ext fun j => ?_⟩
  have hc' := chart_degree (b := 0) ha hb hm (by simpa using hc) j
  have eq := eq_C_of_natDegree_le_zero hc'
  simpa only [coeff_map,coe_evalRingHom,coeff_zero_eq_eval_zero] using eq

/-- Swapping the polynomial variables transposes the coefficient array. -/
theorem swap_coeff (A : Biv) (j k : ℕ) :
    ((Bivariate.swap A).coeff j).coeff k = (A.coeff k).coeff j := by
  induction A using Polynomial.induction_on' with
  | add A B hA hB => simp [hA,hB]
  | monomial i c =>
    induction c using Polynomial.induction_on' with
    | add c d hc hd => simp only [map_add,coeff_add,hc,hd]
    | monomial h c => simp only [Bivariate.swap_monomial_monomial,coeff_monomial]
                      split <;> split <;> simp_all [coeff_monomial]

/-- The upper degree found in the first pair of charts is the strict outer-degree
bound required to compare the second pair of charts after exchanging coordinates. -/
theorem swapped_degree {m b : ℕ} {A B f : Biv} (ha : A.natDegree < f.natDegree)
    (hb : B.natDegree < f.natDegree) (hm : ∀ j, (B.coeff j).natDegree ≤ m)
    (hc : f ∣ C (X^b) * reverseCoeffs m B - C (X^m) * A) :
    (Bivariate.swap A).natDegree ≤ b := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext k
  simpa only [swap_coeff,coeff_zero] using
    (coeff_eq_zero_of_natDegree_lt ((chart_degree ha hb hm hc k).trans_lt hj))

/-- Compare the coordinates on both parameter charts, then compare the parameter
charts themselves. A nonzero quotient rules out every strictly negative twist. -/
theorem four_chart_obstruction {m₁ m₂ m₃ b k : ℕ} (hk : 0<k)
    {A B A' B' f f' : Biv} (ha : A.natDegree < f.natDegree) (hb : B.natDegree < f.natDegree)
    (ha' : A'.natDegree < f'.natDegree) (hb' : B'.natDegree < f'.natDegree)
    (hm₁ : ∀ j, (B.coeff j).natDegree ≤ m₁) (hm₂ : ∀ j, (B'.coeff j).natDegree ≤ m₂)
    (hm₃ : ∀ j, ((Bivariate.swap A').coeff j).natDegree ≤ m₃)
    (h₁ : f ∣ C (X^b)*reverseCoeffs m₁ B - C (X^m₁)*A)
    (h₂ : f' ∣ C (X^b)*reverseCoeffs m₂ B' - C (X^m₂)*A')
    (hr : b < (Bivariate.swap f).natDegree)
    (h₃ : Bivariate.swap f ∣ C 1*reverseCoeffs m₃ (Bivariate.swap A') -
      C (X^(m₃+k))*Bivariate.swap A) : A=0 := by
  have h := negative_twist hk ((swapped_degree ha hb hm₁ h₁).trans_lt hr)
    ((swapped_degree ha' hb' hm₂ h₂).trans_lt hr) hm₃ h₃
  exact Bivariate.swap.injective (by simpa using h.1)

#print axioms chart_degree
#print axioms negative_twist
#print axioms zero_twist
#print axioms swapped_degree
#print axioms four_chart_obstruction

end ArkLib.ProximityGap.Frontier.ApolarReciprocalCharts
