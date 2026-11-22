/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Power sums from the upper coefficients of two split fibers -/

namespace ProximityGap.SplitFiberNewton
open Finset MvPolynomial Polynomial

variable {K I : Type*} [Field K] [Fintype I]

/-- The monic polynomial vanishing at the sites of an indexed fiber,
with multiplicities when the indexing function repeats. -/
noncomputable def vanisher (f : I → K) : K[X] :=
  ((univ.val.map f).map fun z => Polynomial.X - Polynomial.C z).prod

private theorem esymm_of_coeff (f g : I → K) {j : ℕ} (hj : j ≤ Fintype.card I)
    (h : (vanisher f).coeff (Fintype.card I-j) = (vanisher g).coeff (Fintype.card I-j)) :
    aeval f (esymm I K j) = aeval g (esymm I K j) := by
  have coeff (v : I → K) : (vanisher v).coeff (Fintype.card I-j) =
      (-1)^j * (univ.val.map v).esymm j := by
    have rc := Multiset.prod_X_sub_C_coeff (univ.val.map v)
      (k := Fintype.card I-j) (by simp)
    simpa [vanisher, Nat.sub_sub_self hj] using rc
  rw [coeff, coeff] at h
  simpa only [aeval_esymm_eq_multiset_esymm] using
    mul_left_cancel₀ (pow_ne_zero j (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))) h

private theorem psum_of_esymm (f g : I → K) (r : ℕ)
    (h : ∀ d, 0 < d → d ≤ r → aeval f (esymm I K d) = aeval g (esymm I K d)) :
    ∀ d, 0 < d → d ≤ r → aeval f (psum I K d) = aeval g (psum I K d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hr
    rw [psum_eq_mul_esymm_sub_sum I K d hd]
    simp only [map_sub, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast]
    rw [h d hd hr]
    congr 1
    apply sum_congr rfl
    intro a ha
    obtain ⟨ha, hl, hu⟩ := mem_filter.mp ha
    have eq := mem_antidiagonal.mp ha
    rw [h a.1 hl (by omega), ih a.2 (by omega) (by omega) (by omega)]

/-- Equal leading coefficients through depth r give equal positive power sums
through exponent r, in every characteristic. -/
theorem moments_of_coeff (f g : I → K) {r : ℕ} (hr : r ≤ Fintype.card I)
    (h : ∀ j, 0 < j → j ≤ r →
      (vanisher f).coeff (Fintype.card I-j) = (vanisher g).coeff (Fintype.card I-j)) :
    ∀ j, 0 < j → j ≤ r → (∑ i, f i ^ j) = (∑ i, g i ^ j) := by
  intro j hj hle
  have eq := psum_of_esymm f g r (fun d hd h' => esymm_of_coeff f g (h'.trans hr) (h d hd h'))
    j hj hle
  simpa [psum] using eq

/-- A degree drop in the difference of two monic fiber polynomials forces a
matching initial interval of positive power sums. Applying this to the inverse
roots gives the corresponding negative exponents. -/
theorem moments_of_degree_sub (f g : I → K) {e : ℕ} (he : e ≤ Fintype.card I)
    (degree : (vanisher f - vanisher g).natDegree ≤ Fintype.card I - e) :
    ∀ j, 0 < j → j < e → (∑ i, f i ^ j) = (∑ i, g i ^ j) := by
  intro j hj hje
  apply moments_of_coeff f g (r := j) (by omega) _ j hj le_rfl
  intro k _ hkj
  have zero := coeff_eq_zero_of_natDegree_lt
    (show (vanisher f - vanisher g).natDegree < Fintype.card I - k by omega)
  exact sub_eq_zero.mp (by simpa only [coeff_sub] using zero)

#print axioms moments_of_degree_sub
#print axioms moments_of_coeff
end ProximityGap.SplitFiberNewton
