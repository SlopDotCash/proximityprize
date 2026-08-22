/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21QuarticConvolutionCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30IterConvEnergyRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R32LagOffDiagEnergy

/-!
# LANE B2 (#466 round 35): full cyclic convolution energy equals lag-correlation energy

This brick records the finite-algebra identity behind the r = 2/r = 3 bookkeeping:

`∑ d ‖∑ j J(d-j)J(j)‖² = ∑ t ‖∑ j J(j+t)conj(J(j))‖²`.

It is the cyclic convolution/autocorrelation Parseval identity on `ZMod m`, stated without any
analytic input.  The existing `selfConv` used by the punctured Jacobi face removes zero indices;
this full-convolution identity is the clean ambient bridge before boundary corrections are
inserted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy

variable {m : ℕ} [NeZero m]

/-- Full cyclic convolution on `ZMod m`, with no puncturing at the zero index. -/
noncomputable def fullConv (J : ZMod m → ℂ) (d : ZMod m) : ℂ :=
  ∑ j : ZMod m, J (d - j) * J j

/-- Full lag correlation of a cyclic sequence. -/
noncomputable def fullLagCorrelation (J : ZMod m → ℂ) (t : ZMod m) : ℂ :=
  ∑ j : ZMod m, J (j + t) * (starRingEnd ℂ) (J j)

/-- Full cyclic convolution Hermitian energy equals full lag-correlation Hermitian energy. -/
theorem fullConv_hermitianEnergy_eq_fullLagCorrelation_hermitianEnergy (J : ZMod m → ℂ) :
    ∑ d : ZMod m, fullConv J d * (starRingEnd ℂ) (fullConv J d)
      = ∑ t : ZMod m, fullLagCorrelation J t * (starRingEnd ℂ) (fullLagCorrelation J t) := by
  classical
  have hleft :
      (∑ d : ZMod m, fullConv J d * (starRingEnd ℂ) (fullConv J d))
        = ∑ d : ZMod m, ∑ j : ZMod m, ∑ k : ZMod m,
            J (d - j) * J j * ((starRingEnd ℂ) (J (d - k)) * (starRingEnd ℂ) (J k)) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold fullConv
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [map_mul]
  have hright :
      (∑ t : ZMod m, fullLagCorrelation J t * (starRingEnd ℂ) (fullLagCorrelation J t))
        = ∑ t : ZMod m, ∑ j : ZMod m, ∑ k : ZMod m,
            J (j + t) * (starRingEnd ℂ) (J j)
              * ((starRingEnd ℂ) (J (k + t)) * J k) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    unfold fullLagCorrelation
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [map_mul]
    simp
  rw [hleft, hright]
  calc ∑ d : ZMod m, ∑ j : ZMod m, ∑ k : ZMod m,
          J (d - j) * J j * ((starRingEnd ℂ) (J (d - k)) * (starRingEnd ℂ) (J k))
      = ∑ j : ZMod m, ∑ k : ZMod m, ∑ d : ZMod m,
          J (d - j) * J j * ((starRingEnd ℂ) (J (d - k)) * (starRingEnd ℂ) (J k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ j : ZMod m, ∑ k : ZMod m, ∑ i : ZMod m,
          J i * J j * ((starRingEnd ℂ) (J (i + j - k)) * (starRingEnd ℂ) (J k)) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
        refine Fintype.sum_bijective (fun d : ZMod m => d - j) ?_ _ _ ?_
        · refine ⟨?_, ?_⟩
          · intro a b hab
            linear_combination hab
          · intro i
            refine ⟨i + j, ?_⟩
            ring
        · intro d
          congr 3
          · ring_nf
    _ = ∑ j : ZMod m, ∑ t : ZMod m, ∑ i : ZMod m,
          J i * J j * ((starRingEnd ℂ) (J (i - t)) * (starRingEnd ℂ) (J (j + t))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Fintype.sum_bijective (fun k : ZMod m => k - j) ?_ _ _ ?_
        · refine ⟨?_, ?_⟩
          · intro a b hab
            linear_combination hab
          · intro t
            refine ⟨t + j, ?_⟩
            ring
        · intro k
          refine Finset.sum_congr rfl (fun i _ => ?_)
          congr 3
          · ring_nf
          · congr 1
            ring
    _ = ∑ t : ZMod m, ∑ i : ZMod m, ∑ j : ZMod m,
          J i * (starRingEnd ℂ) (J (i - t))
            * ((starRingEnd ℂ) (J (j + t)) * J j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring_nf
    _ = ∑ t : ZMod m, ∑ i : ZMod m, ∑ k : ZMod m,
          J (i + t) * (starRingEnd ℂ) (J i)
            * ((starRingEnd ℂ) (J (k + t)) * J k) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        refine Fintype.sum_bijective (fun i : ZMod m => i - t) ?_ _ _ ?_
        · refine ⟨?_, ?_⟩
          · intro a b hab
            linear_combination hab
          · intro i
            refine ⟨i + t, ?_⟩
            ring
        · intro i
          refine Finset.sum_congr rfl (fun j _ => ?_)
          congr 3
          · ring

/-- Real norm-square form of the full cyclic convolution/autocorrelation identity. -/
theorem fullConv_energy_eq_fullLagCorrelation_energy (J : ZMod m → ℂ) :
    ∑ d : ZMod m, ‖fullConv J d‖ ^ 2
      = ∑ t : ZMod m, ‖fullLagCorrelation J t‖ ^ 2 := by
  classical
  rw [← Complex.ofReal_inj]
  rw [Complex.ofReal_sum, Complex.ofReal_sum]
  calc
    (∑ d : ZMod m, ((‖fullConv J d‖ ^ 2 : ℝ) : ℂ))
        = ∑ d : ZMod m, fullConv J d * (starRingEnd ℂ) (fullConv J d) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [RCLike.mul_conj]
          norm_cast
    _ = ∑ t : ZMod m, fullLagCorrelation J t * (starRingEnd ℂ) (fullLagCorrelation J t) :=
        fullConv_hermitianEnergy_eq_fullLagCorrelation_hermitianEnergy J
    _ = ∑ t : ZMod m, ((‖fullLagCorrelation J t‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [RCLike.mul_conj]
          norm_cast

/-- A uniform pointwise lag-correlation bound gives the corresponding full-convolution
energy bound, with exactly one factor of `m` from summing over the lag parameter. -/
theorem fullConv_energy_bound_of_lagCorrelation_bound (J : ZMod m → ℂ) {B : ℝ}
    (hB : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ B) :
    ∑ d : ZMod m, ‖fullConv J d‖ ^ 2 ≤ (m : ℝ) * B ^ 2 := by
  classical
  rw [fullConv_energy_eq_fullLagCorrelation_energy J]
  have hpoint : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ^ 2 ≤ B ^ 2 := by
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _) (hB t) 2
  calc ∑ t : ZMod m, ‖fullLagCorrelation J t‖ ^ 2
      ≤ ∑ _t : ZMod m, B ^ 2 := Finset.sum_le_sum (fun t _ => hpoint t)
    _ = (m : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [ZMod.card]

/-- The zero lag is controlled by any uniform coefficient envelope. -/
theorem norm_fullLagCorrelation_zero_le_card_mul_sq (J : ZMod m → ℂ)
    {B : ℝ} (hB0 : 0 ≤ B) (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) :
    ‖fullLagCorrelation J 0‖ ≤ (m : ℝ) * B ^ 2 := by
  classical
  calc ‖fullLagCorrelation J 0‖
      ≤ ∑ j : ZMod m, ‖J (j + 0) * (starRingEnd ℂ) (J j)‖ := by
        unfold fullLagCorrelation
        exact norm_sum_le _ _
    _ ≤ ∑ _j : ZMod m, B ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_mul]
        have hstar : ‖(starRingEnd ℂ) (J j)‖ = ‖J j‖ := by simp
        rw [hstar]
        exact (mul_le_mul (hJ (j + 0)) (hJ j) (norm_nonneg _) hB0).trans_eq (by ring)
    _ = (m : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [ZMod.card]

/-- If the zero coefficient vanishes, the punctured convolution used by the Jacobi face is the
same as the full cyclic convolution.  This is the boundary-correction bridge from R21 to R35. -/
theorem selfConv_eq_fullConv_of_zero (J : ZMod m → ℂ) (hJ0 : J 0 = 0) (c : ZMod m) :
    selfConv J c = fullConv J c := by
  classical
  unfold selfConv fullConv
  rw [show (∑ j : ZMod m, J (c - j) * J j)
      = ∑ j : ZMod m, J j * J (c - j) by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    exact Finset.mem_univ j
  · intro j _ hnot
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
      true_and] at hnot
    by_cases hzero : j = 0
    · rw [hzero, hJ0]
      simp
    · have hczero : c - j = 0 := by
        by_contra hc
        exact hnot ⟨hzero, hc⟩
      rw [hczero, hJ0]
      simp

/-- Exact boundary decomposition between the full cyclic convolution and the punctured
R21 convolution.  The only missing summands are the zero-index rows `j = 0` and `j = c`;
when `c = 0` they coincide, so only one boundary term remains. -/
theorem fullConv_eq_selfConv_add_zeroBoundary (J : ZMod m → ℂ) (c : ZMod m) :
    fullConv J c
      = selfConv J c + J c * J 0 + if c = 0 then 0 else J 0 * J c := by
  classical
  unfold fullConv selfConv
  rw [show (∑ j ∈ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0),
        J j * J (c - j))
      = ∑ j ∈ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0),
        J (c - j) * J j by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring]
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    have hfilter :
        (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => 0 - j ≠ 0)
          = (Finset.univ : Finset (ZMod m)).erase 0 := by
      ext j
      simp
    rw [hfilter]
    rw [← Finset.sum_erase_add (Finset.univ : Finset (ZMod m))
      (fun j => J (0 - j) * J j) (Finset.mem_univ (0 : ZMod m))]
    simp
  · have hnot0mem :
        (0 : ZMod m) ∉ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0) := by
      simp
    have hnotcmem :
        c ∉ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0) := by
      simp [hc]
    rw [if_neg hc]
    calc ∑ j : ZMod m, J (c - j) * J j
        = ∑ j ∈ insert (0 : ZMod m) (insert c
              ((Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0))),
            J (c - j) * J j := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro j hj
            exact Finset.mem_univ j
          · intro j _ hnot
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff,
              Finset.mem_univ, Finset.mem_singleton, true_and] at hnot
            by_cases hj0 : j = 0
            · exact (hnot (Or.inl hj0)).elim
            by_cases hjc : j = c
            · exact (hnot (Or.inr (Or.inl hjc))).elim
            have hcj : c - j ≠ 0 := by
              exact sub_ne_zero.mpr (by
                intro h
                exact hjc h.symm)
            exact (hnot (Or.inr (Or.inr ⟨hj0, hcj⟩))).elim
      _ = J c * J 0 + (J 0 * J c
            + ∑ j ∈ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0),
                J (c - j) * J j) := by
          rw [Finset.sum_insert]
          · rw [Finset.sum_insert]
            · ring_nf
            · exact hnotcmem
          · intro h
            rw [Finset.mem_insert] at h
            rcases h with h0c | h0mem
            · exact hc (Eq.symm h0c)
            · exact hnot0mem h0mem
      _ = ∑ j ∈ (Finset.univ \ ({0} : Finset (ZMod m))).filter (fun j => c - j ≠ 0),
            J (c - j) * J j + J c * J 0 + J 0 * J c := by ring

/-- Pointwise norm form of the zero-mode boundary correction.  If all coefficients have norm
at most `B`, then the punctured convolution differs from the full cyclic convolution by at most
`2‖J 0‖B`. -/
theorem norm_selfConv_le_norm_fullConv_add_zeroBoundary (J : ZMod m → ℂ)
    {B : ℝ} (hB0 : 0 ≤ B) (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B) (c : ZMod m) :
    ‖selfConv J c‖ ≤ ‖fullConv J c‖ + 2 * ‖J 0‖ * B := by
  classical
  let bd : ℂ := J c * J 0 + if c = 0 then 0 else J 0 * J c
  have hself : selfConv J c = fullConv J c - bd := by
    dsimp [bd]
    rw [fullConv_eq_selfConv_add_zeroBoundary J c]
    ring
  have hbd : ‖bd‖ ≤ 2 * ‖J 0‖ * B := by
    dsimp [bd]
    by_cases hc : c = 0
    · rw [if_pos hc]
      calc ‖J c * J 0 + 0‖
          = ‖J c * J 0‖ := by rw [add_zero]
        _ = ‖J c‖ * ‖J 0‖ := by rw [norm_mul]
        _ ≤ B * ‖J 0‖ := mul_le_mul_of_nonneg_right (hJ c) (norm_nonneg _)
        _ = ‖J 0‖ * B := by ring
        _ ≤ 2 * ‖J 0‖ * B := by
          have hnon : 0 ≤ ‖J 0‖ * B := mul_nonneg (norm_nonneg _) hB0
          nlinarith
    · rw [if_neg hc]
      calc ‖J c * J 0 + J 0 * J c‖
          ≤ ‖J c * J 0‖ + ‖J 0 * J c‖ := norm_add_le _ _
        _ = ‖J c‖ * ‖J 0‖ + ‖J 0‖ * ‖J c‖ := by rw [norm_mul, norm_mul]
        _ = 2 * ‖J 0‖ * ‖J c‖ := by ring
        _ ≤ 2 * ‖J 0‖ * B := by
          exact mul_le_mul_of_nonneg_left (hJ c) (by positivity)
  calc ‖selfConv J c‖
      = ‖fullConv J c - bd‖ := by rw [hself]
    _ ≤ ‖fullConv J c‖ + ‖bd‖ := norm_sub_le _ _
    _ ≤ ‖fullConv J c‖ + 2 * ‖J 0‖ * B := by nlinarith [hbd]

/-- Squared pointwise form of `norm_selfConv_le_norm_fullConv_add_zeroBoundary`.  This packages
the harmless zero-mode boundary loss in the form used by energy sums. -/
theorem norm_selfConv_sq_le_norm_fullConv_sq_add_zeroBoundary (J : ZMod m → ℂ)
    {B : ℝ} (hB0 : 0 ≤ B) (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B) (c : ZMod m) :
    ‖selfConv J c‖ ^ 2
      ≤ 2 * ‖fullConv J c‖ ^ 2 + 8 * ‖J 0‖ ^ 2 * B ^ 2 := by
  have h := norm_selfConv_le_norm_fullConv_add_zeroBoundary J hB0 hJ c
  have hbd0 : 0 ≤ 2 * ‖J 0‖ * B := by positivity
  have hfull0 : 0 ≤ ‖fullConv J c‖ := norm_nonneg _
  have hself0 : 0 ≤ ‖selfConv J c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖fullConv J c‖ - 2 * ‖J 0‖ * B)]

/-- Energy form of the zero-mode boundary correction.  A full cyclic convolution energy bound
controls the punctured R21 self-convolution energy, up to the explicit boundary term caused by
the two omitted zero summands. -/
theorem selfConv_energy_bound_of_fullConv_energy_and_zeroBoundary (J : ZMod m → ℂ)
    {E B : ℝ} (hB0 : 0 ≤ B) (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hfull : ∑ c : ZMod m, ‖fullConv J c‖ ^ 2 ≤ E) :
    ∑ c : ZMod m, ‖selfConv J c‖ ^ 2
      ≤ 2 * E + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2 := by
  classical
  calc ∑ c : ZMod m, ‖selfConv J c‖ ^ 2
      ≤ ∑ c : ZMod m, (2 * ‖fullConv J c‖ ^ 2 + 8 * ‖J 0‖ ^ 2 * B ^ 2) := by
        exact Finset.sum_le_sum (fun c _ =>
          norm_selfConv_sq_le_norm_fullConv_sq_add_zeroBoundary J hB0 hJ c)
    _ = 2 * ∑ c : ZMod m, ‖fullConv J c‖ ^ 2
          + (m : ℝ) * (8 * ‖J 0‖ ^ 2 * B ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
    _ ≤ 2 * E + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2 := by nlinarith

/-- Budget form of `selfConv_energy_bound_of_fullConv_energy_and_zeroBoundary`, in the exact
`SelfConvEnergyBound` interface consumed by R23's sextic/triple-convolution chain. -/
theorem selfConvEnergyBound_of_fullConv_energy_and_zeroBoundary_budget
    (J : ZMod m → ℂ) (q : ℕ) {E B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hfull : ∑ c : ZMod m, ‖fullConv J c‖ ^ 2 ≤ E)
    (hbudget : 2 * E + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    SelfConvEnergyBound J q C := by
  unfold SelfConvEnergyBound
  exact (selfConv_energy_bound_of_fullConv_energy_and_zeroBoundary J hB0 hJ hfull).trans hbudget

/-- Uniform full lag-correlation control, plus an explicit zero-mode boundary budget, gives the
R23 `SelfConvEnergyBound` input.  This is the direct R35 → R23 consumer bridge. -/
theorem selfConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J : ZMod m → ℂ) (q : ℕ) {L B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    SelfConvEnergyBound J q C :=
  selfConvEnergyBound_of_fullConv_energy_and_zeroBoundary_budget J q hB0 hJ
    (fullConv_energy_bound_of_lagCorrelation_bound J hlag) hbudget

/-- The full R35 → R23 bridge: lag-correlation control, zero-mode bookkeeping, and the usual
coefficient square bound imply the calibrated `TripleConvEnergyBound` input consumed by the
sextic face.  The only analytic content is in the supplied lag and budget hypotheses. -/
theorem tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J : ZMod m → ℂ) (q : ℕ) {L B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    TripleConvEnergyBound J q C :=
  tripleConvEnergyBound_of_selfConvEnergyBound J q hJsq
    (selfConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
      J q hB0 hJ hlag hbudget)

/-- Variant of `tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget` using a
single coefficient envelope `‖J c‖ ≤ B` together with the scalar comparison `B² ≤ q`. -/
theorem tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
    (J : ZMod m → ℂ) (q : ℕ) {L B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B) (hBsq : B ^ 2 ≤ (q : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    TripleConvEnergyBound J q C := by
  have hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
    J q hB0 hJ hJsq hlag hbudget

/-- Lag-correlation control with zero-boundary bookkeeping feeds the final tower at `r = 2`. -/
theorem iterConvEnergyWick_two_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J : ZMod m → ℂ) (q : ℕ) {L B C C₂ : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C₂ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC : C₂ ≤ 2 * C ^ 2) :
    IterConvEnergyWick J q 2 C :=
  iterConvEnergyWick_two_of_selfConvEnergyBound J q
    (selfConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
      J q hB0 hJ hlag hbudget) hC

/-- Lag-correlation control with zero-boundary bookkeeping feeds the final tower at `r = 3`. -/
theorem iterConvEnergyWick_three_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J : ZMod m → ℂ) (q : ℕ) {L B C C₃ : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C₃ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC : C₃ ≤ 6 * C ^ 3) :
    IterConvEnergyWick J q 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound J q
    (tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
      J q hB0 hJ hJsq hlag hbudget) hC

/-- Under `J 0 = 0`, a pointwise lag-correlation bound controls the R21 punctured
self-convolution energy. -/
theorem selfConv_energy_bound_of_lagCorrelation_bound_of_zero (J : ZMod m → ℂ)
    (hJ0 : J 0 = 0) {B : ℝ} (hB : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ B) :
    ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 ≤ (m : ℝ) * B ^ 2 := by
  calc ∑ c : ZMod m, ‖selfConv J c‖ ^ 2
      = ∑ c : ZMod m, ‖fullConv J c‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [selfConv_eq_fullConv_of_zero J hJ0 c]
    _ ≤ (m : ℝ) * B ^ 2 := fullConv_energy_bound_of_lagCorrelation_bound J hB

/-- Zero-mode-free budget form: when `J 0 = 0`, a lag-correlation envelope gives the R23
`SelfConvEnergyBound` input with no boundary correction term. -/
theorem selfConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
    (J : ZMod m → ℂ) (q : ℕ) (hJ0 : J 0 = 0) {L C : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    SelfConvEnergyBound J q C := by
  unfold SelfConvEnergyBound
  exact (selfConv_energy_bound_of_lagCorrelation_bound_of_zero J hJ0 hlag).trans hbudget

/-- Zero-mode-free R35 → R23 bridge.  If `J 0 = 0`, the lag envelope feeds
`TripleConvEnergyBound` without the zero-boundary penalty. -/
theorem tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
    (J : ZMod m → ℂ) (q : ℕ) (hJ0 : J 0 = 0)
    (hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ)) {L C : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    TripleConvEnergyBound J q C :=
  tripleConvEnergyBound_of_selfConvEnergyBound J q hJsq
    (selfConvEnergyBound_of_lagCorrelation_bound_of_zero_budget J q hJ0 hlag hbudget)

/-- Coefficient-envelope variant of the zero-mode-free R35 → R23 bridge. -/
theorem tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
    (J : ZMod m → ℂ) (q : ℕ) (hJ0 : J 0 = 0) {B L C : ℝ}
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B) (hBsq : B ^ 2 ≤ (q : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C * (m : ℝ) * (q : ℝ) ^ 2) :
    TripleConvEnergyBound J q C := by
  have hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
    J q hJ0 hJsq hlag hbudget

/-- Zero-mode-free lag-correlation control feeds the final tower at `r = 2`. -/
theorem iterConvEnergyWick_two_of_lagCorrelation_bound_of_zero_budget
    (J : ZMod m → ℂ) (q : ℕ) (hJ0 : J 0 = 0) {L C C₂ : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C₂ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC : C₂ ≤ 2 * C ^ 2) :
    IterConvEnergyWick J q 2 C :=
  iterConvEnergyWick_two_of_selfConvEnergyBound J q
    (selfConvEnergyBound_of_lagCorrelation_bound_of_zero_budget J q hJ0 hlag hbudget) hC

/-- Zero-mode-free lag-correlation control feeds the final tower at `r = 3`. -/
theorem iterConvEnergyWick_three_of_lagCorrelation_bound_of_zero_budget
    (J : ZMod m → ℂ) (q : ℕ) (hJ0 : J 0 = 0)
    (hJsq : ∀ c : ZMod m, ‖J c‖ ^ 2 ≤ (q : ℝ)) {L C C₃ : ℝ}
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C₃ * (m : ℝ) * (q : ℝ) ^ 2)
    (hC : C₃ ≤ 6 * C ^ 3) :
    IterConvEnergyWick J q 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound J q
    (tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
      J q hJ0 hJsq hlag hbudget) hC

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The zero Jacobi coefficient is the constant term `-1` from the R19 expansion, provided
the multiplicative character is normalized by `χ 1 = 1`. -/
theorem jacobiCoeff_zero_eq_neg_one (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) :
    jacobiCoeff χ lam (0 : ZMod m) = -1 := by
  classical
  unfold jacobiCoeff
  have hpt : ∀ t : F,
      lam 0 t * χ (1 - t) = χ (1 - t) - if t = 0 then χ (1 - t) else 0 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [hfam.map_zero]
    · rw [hfam.triv_on_units t ht]
      simp [ht]
  rw [Finset.sum_congr rfl (fun t _ => hpt t), Finset.sum_sub_distrib]
  rw [sum_shift_eq_zero hχ 1]
  rw [Finset.sum_ite_eq' Finset.univ (0 : F) (fun t => χ (1 - t))]
  simp [hχ1]

/-- Norm form of `jacobiCoeff_zero_eq_neg_one`. -/
theorem norm_jacobiCoeff_zero_eq_one (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) :
    ‖jacobiCoeff χ lam (0 : ZMod m)‖ = 1 := by
  rw [jacobiCoeff_zero_eq_neg_one hχ hχ1 hfam]
  norm_num

/-- Abstract sextic-face consumer from a full-lag envelope and coefficient envelope.  This is
the R35 bridge in the exact R22/R23 face-moment shape, without specializing `J` to Jacobi
coefficients. -/
theorem sextic_moment_of_lagCorrelation_bound_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {L B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_tripleConvEnergyBound hfam hgrp J
    (tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
      J (Fintype.card F) hB0 hJ hBsq hlag hbudget)

/-- Pointwise sixth-power form of
`sextic_moment_of_lagCorrelation_bound_and_coeffEnvelope_budget`. -/
theorem sup_pureFace_of_lagCorrelation_bound_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {L B C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2)
        + (8 * (m : ℝ)) * ‖J 0‖ ^ 2 * B ^ 2
      ≤ C * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_tripleConvEnergyBound hfam hgrp J
    (tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
      J (Fintype.card F) hB0 hJ hBsq hlag hbudget) hs

/-- Abstract sextic consumer in the zero-mode-free case `J 0 = 0`. -/
theorem sextic_moment_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) (hJ0 : J 0 = 0) {B L C : ℝ}
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_tripleConvEnergyBound hfam hgrp J
    (tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
      J (Fintype.card F) hJ0 hJ hBsq hlag hbudget)

/-- Pointwise sixth-power form in the zero-mode-free case `J 0 = 0`. -/
theorem sup_pureFace_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) (hJ0 : J 0 = 0) {B L C : ℝ}
    (hJ : ∀ c : ZMod m, ‖J c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hlag : ∀ t : ZMod m, ‖fullLagCorrelation J t‖ ≤ L)
    (hbudget : (m : ℝ) * L ^ 2 ≤ C * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_tripleConvEnergyBound hfam hgrp J
    (tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
      J (Fintype.card F) hJ0 hJ hBsq hlag hbudget) hs

/-- **Jacobi full-convolution energy from pair-spectrum control.**  R31 supplies the nonzero
lags; the zero-lag/diagonal mass is kept as an explicit input at the same scale. -/
theorem fullJacobiConv_energy_bound_of_twoCharacterWeilInput
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hweil : TwoCharacterWeilInput χ lam G C)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) :
    ∑ d : ZMod m, ‖fullConv (fun i : ZMod m => jacobiCoeff χ lam i) d‖ ^ 2
      ≤ (m : ℝ)
          * (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2) := by
  classical
  let B : ℝ := (m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)
  have hB : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ B := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [fullLagCorrelation, lagCorrelation, B] using hzero
    · have h := lag_correlation_bound hfam hgrp hweil ht
      simpa [fullLagCorrelation, lagCorrelation, B] using h
  simpa [B] using
    (fullConv_energy_bound_of_lagCorrelation_bound
      (J := fun i : ZMod m => jacobiCoeff χ lam i) hB)

/-- **Jacobi/Weil R35 → R23 bridge.**  The R31 two-character Weil input supplies every
nonzero lag; the zero lag and coefficient-size facts are exposed as explicit, checkable
hypotheses.  Under the resulting numeric budget, the Jacobi coefficient sequence satisfies the
R23 `TripleConvEnergyBound` input. -/
theorem tripleConvEnergyBound_of_twoCharacterWeilInput_and_zeroBoundary_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    TripleConvEnergyBound (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) Ctriple := by
  classical
  let L : ℝ := (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)
  have hlag : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ L := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [fullLagCorrelation, lagCorrelation, L] using hzero
    · have h := lag_correlation_bound hfam hgrp hweil ht
      simpa [fullLagCorrelation, lagCorrelation, L] using h
  exact tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J := fun i : ZMod m => jacobiCoeff χ lam i) (q := Fintype.card F)
    (L := L) (B := B) (C := Ctriple) hB0 hJ hJsq hlag (by simpa [L] using hbudget)

/-- Jacobi/Weil bridge with the coefficient square bound derived from one envelope
`‖J_c‖ ≤ B` and `B² ≤ q`. -/
theorem tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    TripleConvEnergyBound (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) Ctriple := by
  classical
  let L : ℝ := (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)
  have hlag : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ L := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [fullLagCorrelation, lagCorrelation, L] using hzero
    · have h := lag_correlation_bound hfam hgrp hweil ht
      simpa [fullLagCorrelation, lagCorrelation, L] using h
  exact tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
    (J := fun i : ZMod m => jacobiCoeff χ lam i) (q := Fintype.card F)
    (L := L) (B := B) (C := Ctriple) hB0 hJ hBsq hlag (by simpa [L] using hbudget)

/-- Jacobi/Weil bridge with the zero-coefficient boundary term evaluated explicitly as `1`.
This is the same as `tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget`,
but callers supply the simpler budget with boundary penalty `8*m*B²`. -/
theorem tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    TripleConvEnergyBound (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) Ctriple := by
  refine tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam := hfam) (hgrp := hgrp) hB0 hJ hBsq hweil hzero ?_
  rw [norm_jacobiCoeff_zero_eq_one hχ hχ1 hfam]
  simpa using hbudget

/-- Jacobi/Weil bridge with no separate zero-lag hypothesis.  The zero lag is bounded from the
coefficient envelope, while R31 supplies the off-zero lags; the uniform lag budget is their max. -/
theorem tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hbudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    TripleConvEnergyBound (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) Ctriple := by
  classical
  let L : ℝ := max ((m : ℝ) * B ^ 2)
    ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
  have hlag : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ L := by
    intro t
    by_cases ht : t = 0
    · subst ht
      exact (norm_fullLagCorrelation_zero_le_card_mul_sq
        (J := fun i : ZMod m => jacobiCoeff χ lam i) hB0 hJ).trans (le_max_left _ _)
    · have h := lag_correlation_bound hfam hgrp hweil ht
      have hoff :
          ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖
            ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) := by
        simpa [fullLagCorrelation, lagCorrelation] using h
      exact hoff.trans (le_max_right _ _)
  refine tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
    (J := fun i : ZMod m => jacobiCoeff χ lam i) (q := Fintype.card F)
    (L := L) (B := B) (C := Ctriple) hB0 hJ hBsq hlag ?_
  rw [norm_jacobiCoeff_zero_eq_one hχ hχ1 hfam]
  simpa [L] using hbudget

/-- Direct depth-two tower consumer for the Jacobi/Weil R35 bridge. -/
theorem iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctwo C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctwo ≤ 2 * C ^ 2) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 C := by
  classical
  let L : ℝ := (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)
  have hlag : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ L := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simpa [fullLagCorrelation, lagCorrelation, L] using hzero
    · have h := lag_correlation_bound hfam hgrp hweil ht
      simpa [fullLagCorrelation, lagCorrelation, L] using h
  exact iterConvEnergyWick_two_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J := fun i : ZMod m => jacobiCoeff χ lam i) (q := Fintype.card F)
    (L := L) (B := B) (C₂ := Ctwo) hB0 hJ hlag (by simpa [L] using hbudget) hC

/-- Direct depth-two tower consumer with the Jacobi zero coefficient evaluated explicitly. -/
theorem iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctwo C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctwo ≤ 2 * C ^ 2) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 C := by
  refine iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam := hfam) (hgrp := hgrp) hB0 hJ hweil hzero ?_ hC
  rw [norm_jacobiCoeff_zero_eq_one hχ hχ1 hfam]
  simpa using hbudget

/-- Direct depth-two tower consumer for the hzero-free max-budget Jacobi/Weil bridge. -/
theorem iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctwo C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hbudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctwo ≤ 2 * C ^ 2) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 C := by
  classical
  let L : ℝ := max ((m : ℝ) * B ^ 2)
    ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
  have hlag : ∀ t : ZMod m,
      ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖ ≤ L := by
    intro t
    by_cases ht : t = 0
    · subst ht
      exact (norm_fullLagCorrelation_zero_le_card_mul_sq
        (J := fun i : ZMod m => jacobiCoeff χ lam i) hB0 hJ).trans (le_max_left _ _)
    · have h := lag_correlation_bound hfam hgrp hweil ht
      have hoff :
          ‖fullLagCorrelation (fun i : ZMod m => jacobiCoeff χ lam i) t‖
            ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) := by
        simpa [fullLagCorrelation, lagCorrelation] using h
      exact hoff.trans (le_max_right _ _)
  refine iterConvEnergyWick_two_of_lagCorrelation_bound_and_zeroBoundary_budget
    (J := fun i : ZMod m => jacobiCoeff χ lam i) (q := Fintype.card F)
    (L := L) (B := B) (C₂ := Ctwo) hB0 hJ hlag ?_ hC
  rw [norm_jacobiCoeff_zero_eq_one hχ hχ1 hfam]
  simpa [L] using hbudget

/-- Direct final-tower consumer for the Jacobi/Weil R35 bridge. -/
theorem iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
      hfam hgrp hB0 hJ hBsq hweil hzero hbudget) hC

/-- Direct final-tower consumer with the Jacobi zero coefficient evaluated explicitly. -/
theorem iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzero hbudget) hC

/-- Direct final-tower consumer for the hzero-free max-budget Jacobi/Weil bridge. -/
theorem iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hbudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hbudget) hC

/-- Direct sextic-face consumer for the Jacobi/Weil R35 bridge.  It composes the
coefficient-envelope triple-convolution bridge with R23's exact sextic collapse. -/
theorem sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
      hfam hgrp hB0 hJ hBsq hweil hzero hbudget)

/-- Direct sextic-face consumer with the Jacobi zero coefficient evaluated explicitly. -/
theorem sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzero hbudget)

/-- Direct sextic-face consumer for the hzero-free max-budget Jacobi/Weil bridge. -/
theorem sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hbudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hbudget)

/-- Pointwise sixth-power consequence for each nonzero Jacobi pure face, under the same R35
coefficient-envelope and Weil hypotheses. -/
theorem sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * ‖jacobiCoeff χ lam 0‖ ^ 2 * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
      hfam hgrp hB0 hJ hBsq hweil hzero hbudget) hs

/-- Pointwise sixth-power consequence with the Jacobi zero coefficient evaluated explicitly. -/
theorem sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzero : ‖lagCorrelation χ lam (0 : ZMod m)‖
      ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hbudget : 2 * ((m : ℝ)
        * (((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzero hbudget) hs

/-- Pointwise sixth-power consequence for the hzero-free max-budget Jacobi/Weil bridge. -/
theorem sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hbudget : 2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_tripleConvEnergyBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    (tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hbudget) hs

end ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms fullConv_hermitianEnergy_eq_fullLagCorrelation_hermitianEnergy
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms fullConv_energy_eq_fullLagCorrelation_energy
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms fullConv_energy_bound_of_lagCorrelation_bound
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms norm_fullLagCorrelation_zero_le_card_mul_sq
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConv_eq_fullConv_of_zero
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms fullConv_eq_selfConv_add_zeroBoundary
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms norm_selfConv_le_norm_fullConv_add_zeroBoundary
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms norm_selfConv_sq_le_norm_fullConv_sq_add_zeroBoundary
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConv_energy_bound_of_fullConv_energy_and_zeroBoundary
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConvEnergyBound_of_fullConv_energy_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_lagCorrelation_bound_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_lagCorrelation_bound_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_two_of_lagCorrelation_bound_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_three_of_lagCorrelation_bound_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConv_energy_bound_of_lagCorrelation_bound_of_zero
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms jacobiCoeff_zero_eq_neg_one
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms norm_jacobiCoeff_zero_eq_one
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms selfConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_two_of_lagCorrelation_bound_of_zero_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_three_of_lagCorrelation_bound_of_zero_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sextic_moment_of_lagCorrelation_bound_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sup_pureFace_of_lagCorrelation_bound_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sextic_moment_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sup_pureFace_of_lagCorrelation_bound_of_zero_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms fullJacobiConv_energy_bound_of_twoCharacterWeilInput
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_twoCharacterWeilInput_and_zeroBoundary_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_budget
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_budget'
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy in
#print axioms sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
