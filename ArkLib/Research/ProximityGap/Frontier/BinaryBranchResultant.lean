/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-! # Resultants of binary projective branch coordinates

A non-monic linear factor aY-b is paired with the original, nominally
homogenized second equation at [b:a]. The coordinates remain integral
even when a vanishes at the center of a completed branch.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BinaryBranchResultant

variable {R : Type*} [CommRing R]

/-- Value of a nominal degree-h binary form at the homogeneous coordinates [x:z]. -/
def binaryValue (G : R[X]) (h : ℕ) (x z : R) : R :=
  G.sum fun j c => c*x^j*z^(h-j)

theorem map_binaryValue {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (G : R[X]) (h : ℕ) (x z : R) :
    φ (binaryValue G h x z) = binaryValue (G.map φ) h (φ x) (φ z) := by
  simp only [binaryValue, Polynomial.sum, map_sum, map_mul, map_pow,
    Polynomial.support_map_of_injective _ hφ, Polynomial.coeff_map]

private theorem linear_resultant_field {K : Type*} [Field K] (G : K[X]) (h : ℕ)
    (hG : G.natDegree ≤ h) (a b : K) (ha : a ≠ 0) :
    (C a*X-C b).resultant G 1 h = binaryValue G h b a := by
  have hf : C a*X-C b = C a*(X-C (b/a)) := by
    rw [mul_sub, ← map_mul, mul_div_cancel₀ b ha]
  rw [hf, resultant_C_mul_left, resultant_X_sub_C_left G h _ hG, eval_eq_sum]
  simp only [binaryValue, Polynomial.sum, Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjh := (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hG
  conv_lhs => lhs; rw [← Nat.sub_add_cancel hjh, pow_add]
  rw [div_pow]
  field_simp

/-- Exact division-free first-order projective intersection identity. -/
theorem linear_resultant [IsDomain R] (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h)
    (a b : R) (ha : a ≠ 0) : (C a*X-C b).resultant G 1 h = binaryValue G h b a := by
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  apply hφ
  rw [map_binaryValue φ hφ, ← resultant_map_map _ _ 1 h φ]
  have hfa : φ a ≠ 0 := by simpa only [map_zero] using hφ.ne ha
  have H : (C a*X-C b).map φ = C (φ a)*X-C (φ b) := by simp
  rw [H]
  exact linear_resultant_field (G.map φ) h (natDegree_map_le.trans hG) (φ a) (φ b) hfa

/-- The resultant in the original affine coordinates equals a product of
homogeneous values, also when some branches pass through the point at infinity. -/
theorem product_resultant [IsDomain R] {ι : Type*} [Fintype ι] (a b : ι → R) (ha : ∀ i, a i ≠ 0)
    (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h) (u : R) :
    (C u*∏ i, (C (a i)*X-C (b i))).resultant G (Fintype.card ι) h =
      u^h*∏ i, binaryValue G h (b i) (a i) := by
  classical
  let f (i : ι) := C (a i)*X-C (b i)
  have hlin (i : ι) : (f i).natDegree = 1 := by
    rw [show f i = _ from rfl, natDegree_sub_eq_left_of_natDegree_lt]
    · simp [ha i]
    · simp [ha i]
  have hlc : ∏ i, (f i).leadingCoeff ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply leadingCoeff_ne_zero.mpr
    intro hi
    simpa [hi] using hlin i
  have hdeg : (∏ i, f i).natDegree = Fintype.card ι := by
    simpa [hlin] using natDegree_prod' univ f hlc
  change (C u*∏ i, f i).resultant G (Fintype.card ι) h = _
  rw [resultant_C_mul_left, ← hdeg, resultant_prod_left _ _ _ _ hlc hG]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [hlin]
  exact linear_resultant G h hG (a i) (b i) (ha i)

/-- Reflecting a product of monic affine sheet equations gives their
homogeneous factors in the original chart. -/
theorem reflect_product {ι : Type*} [IsDomain R] (s : Finset ι) (y : ι → R) :
    (∏ i ∈ s, (X-C (y i))).reflect s.card = ∏ i ∈ s, (1-C (y i)*X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, Nat.add_comm,
      reflect_mul _ _ (natDegree_X_sub_C_le _)]
    · rw [ih]
      congr 1
      rw [sub_eq_add_neg, ← map_neg, reflect_add, reflect_one_X, reflect_C]
      simp [sub_eq_add_neg]
    · have hm : ∀ j ∈ s, (X-C (y j)).Monic := fun j _ => monic_X_sub_C _
      exact (by simpa only [natDegree_prod_of_monic s _ hm, natDegree_X_sub_C,
        sum_const, smul_eq_mul, mul_one] using (le_rfl : s.card ≤ s.card))

/-- Reversing an avoided affine chart and factoring it there gives actual
linear homogeneous factors of the original polynomial. -/
theorem recover_original [IsDomain R] {ι : Type*} [Fintype ι] (F : R[X]) (c v : R) (y : ι → R)
    (hF : (F.taylor c).reflect (Fintype.card ι) = C v*∏ i, (X-C (y i))) :
    F = C v*∏ i, (C (-y i)*X-C (-(1+c*y i))) := by
  classical
  have hh := congrArg (Polynomial.reflect (Fintype.card ι)) hF
  rw [reflect_reflect, reflect_C_mul] at hh
  rw [← Finset.card_univ (α := ι), reflect_product] at hh
  calc
    F = (F.taylor c).comp (X-C c) := by
      rw [taylor_apply, comp_assoc, add_comp, X_comp, C_comp]
      simp
    _ = C v*∏ i, (1-C (y i)*(X-C c)) := by
      simpa only [mul_comp, Polynomial.prod_comp, sub_comp, C_comp, X_comp, one_comp] using
        congrArg (fun p : R[X] => p.comp (X-C c)) hh
    _ = _ := by
      congr 1
      apply prod_congr rfl
      intro i _
      simp only [map_neg, map_add, map_one, map_mul]
      ring

/-- Homogeneity of the nominal binary lift. -/
theorem binaryValue_scale (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h) (u x z : R) :
    binaryValue G h (u*x) (u*z) = u^h*binaryValue G h x z := by
  simp only [binaryValue, Polynomial.sum, Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  have hid := (le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hG
  rw [mul_pow, mul_pow]
  conv_rhs => lhs; rw [← Nat.sub_add_cancel hid, pow_add]
  ring

/-- The finite chart is ordinary polynomial evaluation. -/
theorem binaryValue_unit_right (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h) (u : Rˣ) (x : R) :
    binaryValue G h x u = (u:R)^h * G.eval ((↑u⁻¹:R)*x) := by
  have H := binaryValue_scale G h hG (u:R) ((↑u⁻¹:R)*x) 1
  simpa [binaryValue, eval_eq_sum, ← mul_assoc] using H

/-- The other chart is ordinary evaluation of the nominally reflected form. -/
theorem binaryValue_one_left (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h) (z : R) :
    binaryValue G h 1 z = (G.reflect h).eval z := by
  classical
  have hs (s : Finset ℕ) : (∑ i ∈ s, C (G.coeff i)*X^i).reflect h =
      ∑ i ∈ s, (C (G.coeff i)*X^i).reflect h := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [sum_insert hi, sum_insert hi, reflect_add, ih]
  calc
    _ = ∑ i ∈ G.support, ((C (G.coeff i)*X^i).reflect h).eval z := by
      apply sum_congr rfl
      intro i hi
      have hid := (le_natDegree_of_ne_zero (mem_support_iff.mp hi)).trans hG
      simp [revAt_le hid]
    _ = (G.reflect h).eval z := by
      rw [← Polynomial.eval_finsetSum, ← hs]
      exact congrArg (fun p : R[X] => (p.reflect h).eval z) (sum_C_mul_X_pow_eq G)

theorem binaryValue_unit_left (G : R[X]) (h : ℕ) (hG : G.natDegree ≤ h) (u : Rˣ) (z : R) :
    binaryValue G h u z = (u:R)^h * (G.reflect h).eval ((↑u⁻¹:R)*z) := by
  have H := binaryValue_scale G h hG (u:R) 1 ((↑u⁻¹:R)*z)
  simpa [binaryValue_one_left G h hG, ← mul_assoc] using H

#print axioms binaryValue_unit_right
#print axioms binaryValue_unit_left
#print axioms recover_original
#print axioms linear_resultant
#print axioms product_resultant

end ArkLib.ProximityGap.Frontier.BinaryBranchResultant
