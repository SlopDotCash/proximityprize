/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ImplicitDerivativeNumerator
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions
import ArkLib.ToMathlib.BivariateDegreeToolkit

/-! # Degree growth of the actual implicit derivative numerator

For coordinate differentiation fixing the scalar parameter, an equation of
total degree five and value degree three has order-`j+1` implicit derivative
numerator of total degree at most `5+8*j` and value degree at most `3+4*j`.
The resultant of the equation and this numerator has scalar degree at most
`21+32*j`. All three bounds allow degree drops in positive characteristic.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Polynomial.Bivariate ArkLib.BivariateDegreeToolkit
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.ImplicitDerivativeBidegree

open ImplicitDerivativeNumerator WeightedSylvesterDegree

variable {K : Type} [Field K]

/-- Extend a derivation to polynomial coefficients while fixing the scalar indeterminate. -/
@[instance_reducible] def coefficientDifferential [Differential K] : Differential K[X] := ⟨Differential.mapCoeffs⟩

theorem natDegree_mapCoeffs_le [Differential K] (p : K[X]) :
    (Differential.mapCoeffs p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [coeff_eq_zero_of_natDegree_lt hi]

section DegreeGrowth

variable [Differential K[X]] (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)

include hD in
private theorem map_weight_le (p : K[X][X]) (u : ℕ) :
    natWeightedDegree (Differential.mapCoeffs p) u 1 ≤ natWeightedDegree p u 1 := by
  refine Finset.sup_le fun i hi => ?_
  have hi' : p.coeff i ≠ 0 := by
    rw [mem_support_iff] at hi
    intro h
    simp [h] at hi
  simpa only [Differential.coeff_mapCoeffs] using
    (Nat.add_le_add_right (Nat.mul_le_mul_left u (hD (p.coeff i))) (1*i)).trans
      (weight_coeff_le_natWeightedDegree p u 1 (mem_support_iff.mpr hi'))

omit [Differential K[X]] in
private theorem derivative_weight_le (p : K[X][X]) (u m : ℕ)
    (hp : natWeightedDegree p u 1 ≤ m) :
    natWeightedDegree p.derivative u 1 ≤ m-1 := by
  refine Finset.sup_le fun i hi => ?_
  have hi' : p.coeff (i+1) ≠ 0 := by
    rw [mem_support_iff] at hi
    intro h
    simp [coeff_derivative, h] at hi
  have hb := (weight_coeff_le_natWeightedDegree p u 1 (mem_support_iff.mpr hi')).trans hp
  have hd := Nat.mul_le_mul_left u (Polynomial.coeff_derivative_natDegree_le p i)
  simp only [one_mul] at hb ⊢
  omega

omit [Differential K[X]] in
private theorem sub_weight_le (p q : K[X][X]) (u a : ℕ)
    (hp : natWeightedDegree p u 1 ≤ a) (hq : natWeightedDegree q u 1 ≤ a) :
    natWeightedDegree (p-q) u 1 ≤ a := by
  rw [sub_eq_add_neg]
  apply (GuruswamiSudan.natWeightedDegree_add_le _ _ _ _).trans
  apply max_le hp
  simpa [natWeightedDegree] using hq

include hD in
private theorem along_weight_le (f p : K[X][X]) {u a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hf : natWeightedDegree f u 1 ≤ a)
    (hp : natWeightedDegree p u 1 ≤ b) : natWeightedDegree (along f p) u 1 ≤ a+b-1 := by
  apply sub_weight_le
  · apply (natWeightedDegree_mul_le _ _ _ _).trans
    have h₁ := derivative_weight_le f u a hf
    have h₂ := (map_weight_le hD p u).trans hp
    omega
  · apply (natWeightedDegree_mul_le _ _ _ _).trans
    have h₁ := (map_weight_le hD f u).trans hf
    have h₂ := derivative_weight_le p u b hp
    omega

include hD in
/-- Weighted degree in the scalar and value variables after repeated implicit
differentiation. The value variable has weight one. -/
theorem numerator_weight_le (f : K[X][X]) {u m : ℕ} (hm : 2 ≤ m)
    (hf : natWeightedDegree f u 1 ≤ m) (j : ℕ) :
    natWeightedDegree (numerator f j) u 1 ≤ m+2*j*(m-1) := by
  induction j with
  | zero =>
      simpa [numerator, natWeightedDegree] using (map_weight_le hD f u).trans hf
  | succ j ih =>
      have hd := derivative_weight_le f u m hf
      have ha := along_weight_le hD f (numerator f j) (by omega) (by omega) hf ih
      have hb := along_weight_le hD f f.derivative (by omega) (by omega) hf hd
      rw [numerator]
      apply sub_weight_le
      · apply (natWeightedDegree_mul_le _ _ _ _).trans
        rw [Nat.mul_succ, Nat.add_mul]
        omega
      · apply (natWeightedDegree_mul_le _ _ _ _).trans
        have hn := GuruswamiSudan.OverRatFunc.natWeightedDegree_C_C_mul_le
          (↑(2*j+1) : K) (numerator f j) u 1
        have hc : Polynomial.C (Polynomial.C (↑(2*j+1) : K)) =
            (↑(2*j+1) : K[X][X]) := by rw [map_natCast, map_natCast]
        rw [hc] at hn
        rw [Nat.mul_succ, Nat.add_mul]
        omega

omit [Differential K[X]] in
private theorem total_iff_weight (p : K[X][X]) (m : ℕ) :
    TotalDegreeLe p m ↔ natWeightedDegree p 1 1 ≤ m := by
  constructor
  · intro h
    exact Finset.sup_le fun i hi => by simpa using h i (mem_support_iff.mp hi)
  · intro h i hi
    simpa using (weight_coeff_le_natWeightedDegree p 1 1 (mem_support_iff.mpr hi)).trans h

include hD in
/-- Total and value degree of the actual numerator for a quintic of value degree three. -/
theorem quintic_cubic_numerator (f : K[X][X]) (j : ℕ)
    (hf : TotalDegreeLe f 5) (hfy : f.natDegree ≤ 3) :
    TotalDegreeLe (numerator f j) (5+8*j) ∧ (numerator f j).natDegree ≤ 3+4*j := by
  constructor
  · apply (total_iff_weight _ _).mpr
    convert numerator_weight_le hD f (by decide : 2 ≤ 5) ((total_iff_weight _ _).mp hf) j
      using 1
    omega
  · change natDegreeY (numerator f j) ≤ 3+4*j
    rw [degreeY_as_weighted_deg]
    change natDegreeY f ≤ 3 at hfy
    rw [degreeY_as_weighted_deg] at hfy
    convert numerator_weight_le hD f (by decide : 2 ≤ 3) hfy j using 1
    omega

include hD in
/-- The weighted Sylvester bound applied to the recursive numerator itself. -/
theorem quintic_cubic_resultant (f : K[X][X]) (j : ℕ)
    (hf : TotalDegreeLe f 5) :
    (resultant f (numerator f j) 3 (3+4*j)).natDegree ≤ 21+32*j := by
  apply quintic_cubic_derivative_resultant_bound _ _ _ hf
  apply (total_iff_weight _ _).mpr
  convert numerator_weight_le hD f (by decide : 2 ≤ 5) ((total_iff_weight _ _).mp hf) j
    using 1
  omega

private theorem cubic_degree_arithmetic {b c j : ℕ} (hb : b ≤ 3) (hc : c ≤ 3+4*j) :
    b*(5+8*j) + c*5 - b*c ≤ 21+32*j := by
  have h := Nat.sub_add_cancel (by omega : c ≤ 5+8*j)
  have he : b*(5+8*j) = b*(5+8*j-c) + b*c := by
    rw [← Nat.mul_add, h]
  have hh := Nat.mul_le_mul_right (5+8*j-c) hb
  omega

include hD in
/-- The resultant of the actual value degrees has the same bound when either
leading coefficient vanishes. This is the resultant used for a common-factor inference. -/
theorem quintic_cubic_actual_resultant (f : K[X][X]) (j : ℕ)
    (hf : TotalDegreeLe f 5) (hfy : f.natDegree ≤ 3) :
    (resultant f (numerator f j) f.natDegree (numerator f j).natDegree).natDegree ≤
      21+32*j := by
  obtain ⟨ht, hy⟩ := quintic_cubic_numerator hD f j hf hfy
  apply (natDegree_resultant_le f (numerator f j) hf ht).trans
  exact cubic_degree_arithmetic hfy hy

include hD in
/-- More than `21+32*j` distinct common fibers force the actual-degree derivative
resultant to vanish. A positive value degree excludes the empty Sylvester matrix. -/
theorem quintic_cubic_resultant_zero_of_common_fibers (f : K[X][X]) (j : ℕ)
    (hf : TotalDegreeLe f 5) (hfy : f.natDegree ≤ 3) (hpos : f.natDegree ≠ 0)
    (S : Finset K) (hS : ∀ z ∈ S, ∃ y : K, (f.map (evalRingHom z)).eval y = 0 ∧
      ((numerator f j).map (evalRingHom z)).eval y = 0)
    (hcard : 21+32*j < S.card) :
    resultant f (numerator f j) f.natDegree (numerator f j).natDegree = 0 := by
  by_contra hn
  obtain ⟨ht, hy⟩ := quintic_cubic_numerator hD f j hf hfy
  have hh := common_fiber_count f (numerator f j) le_rfl le_rfl (Or.inl hpos)
    hf ht hn S hS
  exact (Nat.not_lt_of_ge (hh.trans (cubic_degree_arithmetic hfy hy))) hcard

end DegreeGrowth

/-- With the coefficientwise extension, the degree hypothesis follows from the
definition of the derivation. -/
theorem coefficientDifferential_degree [Differential K] (q : K[X]) :
    letI := coefficientDifferential (K := K)
    q′.natDegree ≤ q.natDegree :=
  natDegree_mapCoeffs_le q

/-- Distinct constant parameters carrying roots with vanishing coordinate derivative
force the actual derivative resultant to vanish. The degree bounds do not require
a nonzero value derivative at those roots. -/
theorem quintic_cubic_resultant_zero_of_derivative_roots [Differential K]
    (f : K[X][X]) (j : ℕ) (hf : TotalDegreeLe f 5) (hfy : f.natDegree ≤ 3)
    (hpos : f.natDegree ≠ 0) (S : Finset K) (hS : ∀ z ∈ S, z′ = 0 ∧ ∃ y : K,
      (f.map (evalRingHom z)).eval y = 0 ∧ (Differential.deriv^[j+1]) y = 0)
    (hcard : 21+32*j < S.card) :
    letI := coefficientDifferential (K := K)
    resultant f (numerator f j) f.natDegree (numerator f j).natDegree = 0 := by
  let _ : Differential K[X] := coefficientDifferential (K := K)
  apply quintic_cubic_resultant_zero_of_common_fibers coefficientDifferential_degree
    f j hf hfy hpos S _ hcard
  intro z hz
  obtain ⟨hc, y, hy, hd⟩ := hS z hz
  refine ⟨y, hy, ?_⟩
  let _ : Algebra K[X] K := (evalRingHom z).toAlgebra
  let _ : DifferentialAlgebra K[X] K := ⟨fun p => by
    change (p.eval z)′ = (Differential.mapCoeffs p).eval z
    simpa [hc] using (Differential.deriv_aeval_eq z p)⟩
  have hev (p : K[X][X]) : aeval y p = (p.map (evalRingHom z)).eval y := by
    rw [aeval_def, eval_map]
    rfl
  rw [← hev] at hy ⊢
  exact numerator_aeval_zero _ _ hy _ hd

/-- In any fraction field of the scalar polynomial ring, irreducibility turns
vanishing of the actual resultant into divisibility by the equation. -/
theorem quintic_cubic_dvd_of_derivative_roots [Differential K] {L : Type*} [Field L]
    (φ : K[X] →+* L) (hφ : Function.Injective φ) (f : K[X][X]) (j : ℕ)
    (hf : TotalDegreeLe f 5) (hfy : f.natDegree ≤ 3) (hpos : f.natDegree ≠ 0)
    (hirr : Irreducible (f.map φ)) (S : Finset K)
    (hS : ∀ z ∈ S, z′ = 0 ∧ ∃ y : K, (f.map (evalRingHom z)).eval y = 0 ∧
      (Differential.deriv^[j+1]) y = 0) (hcard : 21+32*j < S.card) :
    letI := coefficientDifferential (K := K)
    f.map φ ∣ (numerator f j).map φ := by
  let _ : Differential K[X] := coefficientDifferential (K := K)
  have hz := quintic_cubic_resultant_zero_of_derivative_roots f j hf hfy hpos S hS hcard
  apply hirr.dvd_iff_not_isCoprime.mpr
  apply (resultant_eq_zero_iff.mp _).2
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ, resultant_map_map]
  exact (congrArg φ hz).trans (map_zero φ)

end ArkLib.ProximityGap.Frontier.ImplicitDerivativeBidegree

open ArkLib.ProximityGap.Frontier.ImplicitDerivativeBidegree in
#print axioms quintic_cubic_dvd_of_derivative_roots
