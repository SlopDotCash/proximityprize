/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarParameterTransition

/-! # Reciprocal descent at equal coordinate degree

When the locator coefficients span every parameter polynomial of degree at
most m+1, the cleared quotient still vanishes at coordinate degree equal to
the locator degree, provided the two parameter ranges are separated by a gap.
-/

set_option autoImplicit false
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.ApolarBorderDescent
open ApolarReciprocalCharts
variable {K : Type*} [Field K]
local notation "Biv" => K[X][X]

/-- A missing band in the coefficients of each locator multiple detects every
coefficient of the scalar quotient, by multiplying by appropriate monomials. -/
private theorem quotient_zero (f : Biv) (g : K[X]) (m k : ℕ) (hk : 2 ≤ k)
    (span : ∀ i ≤ m+1, ∃ c : Fin (f.natDegree+1) → K,
      ∑ j, C (c j)*f.coeff j.val = X^i)
    (gap : ∀ j s : ℕ, m < s → (s < m+k ∨ 2*m+k < s) → (f.coeff j*g).coeff s=0) : g=0 := by
  classical
  ext t
  have miss (i : ℕ) (hi : i≤m+1) (hs : m<t+i)
      (hband : t+i<m+k ∨ 2*m+k<t+i) : g.coeff t=0 := by
    obtain ⟨c,hc⟩ := span i hi
    have h := congrArg (fun R : K[X] => (R*g).coeff (t+i)) hc
    simp only [Finset.sum_mul,mul_assoc,finsetSum_coeff,coeff_C_mul,coeff_X_pow_mul,
      gap _ _ hs hband,mul_zero,Finset.sum_const_zero] at h
    exact h.symm
  by_cases h : t<m+k
  · simpa only [coeff_zero] using miss (m+1-t) (by omega) (by omega) (Or.inl (by omega))
  · simpa only [coeff_zero] using miss (m+1) le_rfl (by omega) (Or.inr (by omega))

/-- Sharp negative-twist comparison in the borderline coordinate degree. -/
theorem negative_twist_equal (f A B : Biv) {m k : ℕ} (hk : 2≤k)
    (ha : A.natDegree ≤ f.natDegree) (hb : B.natDegree ≤ f.natDegree)
    (hA : ∀ j, (A.coeff j).natDegree ≤ m) (hB : ∀ j, (B.coeff j).natDegree ≤ m)
    (span : ∀ i ≤ m+1, ∃ c : Fin (f.natDegree+1) → K,
      ∑ j, C (c j)*f.coeff j.val = X^i)
    (h : f ∣ C 1*reverseCoeffs m B - C (X^(m+k))*A) : A=0 ∧ B=0 := by
  classical
  simp only [map_one,one_mul] at h
  obtain ⟨U,hU⟩ := h
  have hr : (reverseCoeffs m B).natDegree ≤ f.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [coeff_eq_zero_of_natDegree_lt (hb.trans_lt hj)]
  have hf : f≠0 := by
    intro hz
    obtain ⟨c,hc⟩ := span 0 (by omega)
    simp [hz] at hc
  have hdeg : U.natDegree=0 := by
    by_cases hu : U=0
    · simp [hu]
    have hh := (natDegree_sub_le (reverseCoeffs m B) (C (X^(m+k))*A)).trans
      (max_le hr ((natDegree_C_mul_le ..).trans ha))
    rw [hU,natDegree_mul hf hu] at hh
    omega
  let g := U.coeff 0
  have hcu : U=C g := eq_C_of_natDegree_eq_zero hdeg
  rw [hcu] at hU
  have coeffEq (j : ℕ) :
      reflect m (B.coeff j) - X^(m+k)*A.coeff j = f.coeff j*g := by
    simpa only [coeff_sub,coeff_reverseCoeffs,coeff_C_mul,coeff_mul_C] using
      congrArg (fun R : Biv => R.coeff j) hU
  have hrdeg (j : ℕ) : (reflect m (B.coeff j)).natDegree ≤ m :=
    natDegree_reflect_le.trans (max_le le_rfl (hB j))
  have hg : g=0 := by
    apply quotient_zero f g m k hk span
    intro j s hs hband
    rw [← coeffEq,coeff_sub,coeff_eq_zero_of_natDegree_lt ((hrdeg j).trans_lt hs),coeff_X_pow_mul']
    rcases hband with hlow | hhigh
    · simp [Nat.not_le.mpr hlow]
    · simp only [show m+k≤s by omega, ite_true, coeff_eq_zero_of_natDegree_lt
        ((hA j).trans_lt (show m<s-(m+k) by omega)),sub_zero]
  have hz (j : ℕ) : A.coeff j = 0 := by
    by_contra hne
    have h := coeffEq j
    rw [hg,mul_zero,sub_eq_zero] at h
    have hh := hrdeg j
    rw [h,natDegree_mul (pow_ne_zero _ X_ne_zero) hne,natDegree_X_pow] at hh
    omega
  refine ⟨Polynomial.ext fun j => by simp [hz],Polynomial.ext fun j => ?_⟩
  have h := coeffEq j
  simpa [hz,hg] using h

/-- The cleared parameter-chart remainders both vanish at the borderline. -/
theorem vanish_of_cleared (f B Bt : Biv) (u : K[X]ˣ) {m k : ℕ} (hk : 2≤k)
    (hb : (Bivariate.swap B).natDegree ≤ f.natDegree)
    (hbt : (Bivariate.swap Bt).natDegree ≤ f.natDegree)
    (hm : B.natDegree≤m) (hm' : Bt.natDegree≤m)
    (span : ∀ i ≤ m+1, ∃ c : Fin (f.natDegree+1) → K,
      ∑ j, C (c j)*f.coeff j.val = X^i)
    (h : f ∣ C 1*reverseCoeffs m (Bivariate.swap (C (u:K[X])*Bt)) -
      C (X^(m+k))*Bivariate.swap B) : B=0 ∧ Bt=0 := by
  have hu := _root_.ProximityGap.ApolarParameterTransition.unit_rescale_degrees u Bt
  have height (R : Biv) (hR : R.natDegree≤m) (j : ℕ) :
      ((Bivariate.swap R).coeff j).natDegree≤m := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro v hv
    rw [swap_coeff,coeff_eq_zero_of_natDegree_lt (hR.trans_lt hv),coeff_zero]
  obtain ⟨hB,hBt⟩ := negative_twist_equal f _ _ hk hb (hu.2.trans_le hbt)
    (height B hm) (height _ (hu.1.trans_le hm')) span h
  have hs : C (u:K[X])*Bt = 0 := Bivariate.swap.injective (by simpa using hBt)
  exact ⟨Bivariate.swap.injective (by simpa using hB),
    (mul_eq_zero.mp hs).resolve_left (C_ne_zero.mpr u.ne_zero)⟩

#print axioms negative_twist_equal
#print axioms vanish_of_cleared
end ArkLib.ProximityGap.Frontier.ApolarBorderDescent
