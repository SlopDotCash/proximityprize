/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleySliceSampling
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftFactorization
import Mathlib.Analysis.Real.Sqrt

/-! # Absolute row mass on a prescribed cardinality slice

For zero-mean weights, fixed-size signed sums control the total absolute weight
of any fixed-size selection. In the Paley application each absolute weight is
recovered from the corresponding interpolation determinant's root multiplicity.
-/

namespace ProximityGap.PaleyAbsoluteSlice

open Finset PaleyShiftMultiplicityBudget PaleyShiftFactorization
open ArkLib.ProximityGap.Frontier.PaleySliceSampling

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem compl_sum (w : X → ℝ) (hw : ∑ i, w i = 0) (U : Finset X) :
    ∑ i ∈ Uᶜ, w i = -(∑ i ∈ U, w i) := by
  have h := sum_add_sum_compl U w
  rw [hw] at h
  linarith

/-- A bound on all signed sums of size `m` bounds each smaller signed sum
with its exact finite-population correction. -/
theorem signed_subset (w : X → ℝ) (hw : ∑ i, w i = 0) {m : ℕ} (hm : m < Fintype.card X)
    {H : ℝ} (hH : ∀ S : Finset X, S.card = m → |∑ i ∈ S, w i| ≤ H)
    (U : Finset X) (hU : U.card ≤ m) :
    |∑ i ∈ U, w i| * ((Fintype.card X : ℝ)-m) ≤ ((Fintype.card X : ℝ)-U.card)*H := by
  have h := abs_sum_mul_card_sample w Uᶜ (m := Fintype.card X-m) (by omega)
    (by rw [card_compl]; omega) (b := H) (by
      intro S hS
      have hcard := (mem_powersetCard.mp hS).2
      have hc := hH Sᶜ (by rw [card_compl]; omega)
      rwa [compl_sum w hw, abs_neg] at hc)
  rwa [compl_sum w hw, abs_neg, card_compl, Nat.cast_sub hm.le, Nat.cast_sub U.card_le_univ] at h

/-- The sum of the absolute values at any `m` sites is bounded by the maximum signed
sum on the slice times `(2*N-m)/(N-m)`, with the denominator cleared. -/
theorem absolute_slice (w : X → ℝ) (hw : ∑ i, w i = 0) {m : ℕ} (hm : m < Fintype.card X)
    {H : ℝ} (hH : ∀ S : Finset X, S.card = m → |∑ i ∈ S, w i| ≤ H)
    (T : Finset X) (hT : T.card = m) :
    (∑ i ∈ T, |w i|) * ((Fintype.card X : ℝ)-m) ≤ (2*Fintype.card X - (m:ℝ))*H := by
  let P := T.filter fun i => 0 ≤ w i
  let Q := T.filter fun i => ¬ 0 ≤ w i
  have hsP : P ⊆ T := filter_subset _ _
  have hsQ : Q ⊆ T := filter_subset _ _
  have hP := signed_subset w hw hm hH P ((card_le_card hsP).trans hT.le)
  have hQ := signed_subset w hw hm hH Q ((card_le_card hsQ).trans hT.le)
  have hsgnP (i : X) (hi : i ∈ P) : 0 ≤ w i := (mem_filter.mp hi).2
  have hsgnQ (i : X) (hi : i ∈ Q) : w i ≤ 0 := (lt_of_not_ge (mem_filter.mp hi).2).le
  rw [abs_of_nonneg (sum_nonneg hsgnP)] at hP
  rw [abs_of_nonpos (sum_nonpos hsgnQ)] at hQ
  have hsplit := sum_filter_add_sum_filter_not T (fun i => 0 ≤ w i) (fun i => |w i|)
  change (∑ i ∈ P, |w i|) + (∑ i ∈ Q, |w i|) = _ at hsplit
  rw [sum_congr rfl (fun i hi => abs_of_nonneg (hsgnP i hi)),
    sum_congr rfl (fun i hi => abs_of_nonpos (hsgnQ i hi)), sum_neg_distrib] at hsplit
  have hcard : (P.card : ℝ)+Q.card=m := by
    exact_mod_cast (card_filter_add_card_filter_not (s := T) (fun i => 0 ≤ w i)).trans hT
  rw [← hsplit]
  nlinarith only [hP,hQ,congrArg (· * H) hcard]

variable {p : ℕ} [Fact p.Prime]

/-- Every selection of `m` shifts has its unsigned row mass controlled by a bound on
the signed discrepancy over all selections of the same size. -/
theorem absolute_shifts (hp : p ≠ 2) (A : Finset (ZMod p)) {m : ℕ} (hm : m < p)
    {H : ℝ} (hH : ∀ S : Finset (ZMod p), S.card = m → |∑ b ∈ S, (shiftSum A b : ℝ)| ≤ H)
    (T : Finset (ZMod p)) (hT : T.card = m) :
    (∑ b ∈ T, |(shiftSum A b : ℝ)|) * ((p:ℝ)-m) ≤ (2*p - (m:ℝ))*H := by
  have hz := congrArg (fun t : ℤ => (t : ℝ)) (sum_shift hp A)
  simp only [Int.cast_sum, Int.cast_zero] at hz
  simpa only [ZMod.card] using
    absolute_slice (fun b => (shiftSum A b : ℝ)) hz
      (by simpa only [ZMod.card] using hm) hH T hT

/-- Absolute magnitude recovered from the interpolation determinant and zero-symbol parity. -/
noncomputable def rootWeight (A : Finset (ZMod p)) (b : ZMod p) : ℝ :=
  Real.sqrt (4*((central A).rootMultiplicity b : ℝ) +
    (((A.card - (if -b ∈ A then 1 else 0)) % 2 : ℕ) : ℝ))

/-- At every shift the parity-corrected square root is exactly the absolute row sum. -/
theorem rootWeight_eq (hp : p ≠ 2) (A : Finset (ZMod p)) (ha : 2 ≤ A.card)
    (ha' : A.card ≤ p/2+1) (b : ZMod p) : rootWeight A b = |(shiftSum A b : ℝ)| := by
  let w := shiftSum A b
  let z : ℕ := if -b ∈ A then 1 else 0
  have he := PaleyShiftListRecovery.agreement_excess A b (s := 1) (Or.inl rfl)
  change 1*w = _ at he
  have hpar : w % 2 = (((A.card-z)%2 : ℕ) : ℤ) := by
    dsimp only [z]
    split_ifs at he ⊢ <;> omega
  have hfloor : 4*(w^2/4) + w%2 = w^2 := by linarith only [four_mul_floor w]
  rw [hpar] at hfloor
  unfold rootWeight
  rw [rootMultiplicity_central hp A ha ha' b]
  change Real.sqrt (4*(((w^2/4).toNat : ℕ) : ℝ) + (((A.card-z)%2 : ℕ) : ℝ)) = |(w : ℝ)|
  rw [← Real.sqrt_sq_eq_abs (w : ℝ)]
  congr 1
  have hnat := Int.toNat_of_nonneg (Int.ediv_nonneg (sq_nonneg w) (by decide : (0:ℤ) ≤ 4))
  have h' : 4*(((w^2/4).toNat : ℕ) : ℤ) + (((A.card-z)%2 : ℕ) : ℤ) = w^2 := by
    rwa [hnat]
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast]
    using congrArg (fun t : ℤ => (t : ℝ)) h'

/-- Bounds on signed sums for every size-`m` test set control the largest possible mass
of any `m` parity-corrected determinant root weights. -/
theorem root_mass_of_signed (hp : p ≠ 2) (A : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) {m : ℕ} (hm : m < p)
    {H : ℝ} (hH : ∀ S : Finset (ZMod p), S.card = m → |∑ b ∈ S, (shiftSum A b : ℝ)| ≤ H)
    (T : Finset (ZMod p)) (hT : T.card = m) :
    (∑ b ∈ T, rootWeight A b) * ((p:ℝ)-m) ≤ (2*p-(m:ℝ))*H := by
  simp_rw [rootWeight_eq hp A ha ha']
  exact absolute_shifts hp A hm hH T hT

/-- Uniform size-`m` root-mass estimates control every prescribed rectangle whose two
sides have at least `m` elements, at the same relative scale. -/
theorem discrepancy_of_root_mass (hp : p ≠ 2) {m : ℕ} (hm : 2 ≤ m) (hm' : m ≤ p/2+1)
    {H : ℝ} (hH : ∀ X Y : Finset (ZMod p), X.card=m → Y.card=m → ∑ b ∈ Y, rootWeight X b ≤ H)
    (A B : Finset (ZMod p)) (hA : m ≤ A.card) (hB : m ≤ B.card) :
    |∑ b ∈ B, (shiftSum A b : ℝ)| * (m : ℝ)^2 ≤ H*A.card*B.card := by
  have hm1 : 1 ≤ m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hfixed (X Y : Finset (ZMod p)) (hX : X.card = m) (hY : Y.card = m) :
      |∑ b ∈ Y, (shiftSum X b : ℝ)| ≤ H := by
    have h := hH X Y hX hY
    simp_rw [rootWeight_eq hp X (hX ▸ hm) (hX ▸ hm')] at h
    exact (abs_sum_le_sum_abs _ _).trans h
  have hpart (Y : Finset (ZMod p)) (hY : Y ∈ B.powersetCard m) :
      |∑ b ∈ Y, (shiftSum A b : ℝ)| ≤ A.card*H/m := by
    apply (le_div_iff₀ hmr).mpr
    simp only [shiftSum, Int.cast_sum]
    rw [sum_comm]
    apply abs_sum_mul_card_sample _ A hm1 hA
    intro X hX
    rw [sum_comm]
    simpa only [shiftSum, Int.cast_sum] using hfixed X Y (mem_powersetCard.mp hX).2
      (mem_powersetCard.mp hY).2
  have h := abs_sum_mul_card_sample (fun b => (shiftSum A b : ℝ)) B hm1 hB hpart
  calc
    _ = (|∑ b ∈ B, (shiftSum A b : ℝ)| * m) * m := by ring
    _ ≤ (B.card*(A.card*H/m))*m := mul_le_mul_of_nonneg_right h hmr.le
    _ = _ := by field_simp

#print axioms absolute_slice
#print axioms root_mass_of_signed
#print axioms discrepancy_of_root_mass

end ProximityGap.PaleyAbsoluteSlice
