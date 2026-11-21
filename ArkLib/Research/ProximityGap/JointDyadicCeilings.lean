/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointAdjacentFieldReview
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup
import ArkLib.Research.ProximityGap.Frontier.BoundaryFullMass
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent

/-! # Sharp dyadic lengths for the joint large-field answers

At 128-bit tolerance with field size below `2^256`, the simultaneous outcome
of radius-one MCA safety and first list failure at minimum distance is possible
exactly through length 128 at rates 1/2, 1/4, 1/8, and through 256 at rate 1/16.
The scalar field of BLS12-381 realizes every eligible length within these limits.
-/

namespace ProximityPrize.JointDyadicCeilings

open Code ProximityGap FullPrizeReview
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- The joint outcome whose occurrence is decided by the two binomial counts. -/
def joint (D : I ↪ F) (k m : ℕ) : Prop :=
  RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none ∧
    (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
      some (Fintype.card I - k + 1)

/-- Admissible dyadic lengths for the joint outcome at an eligible rate. -/
def withinCeiling (n k : ℕ) : Prop := n ≤ 128 ∨ (16 * k = n ∧ n ≤ 256)

private theorem pow2_jump {t a b : ℕ} (hp : b = 2 ^ t) (h : 2 ^ a < b) :
    2 ^ (a + 1) ≤ b := by
  subst b
  exact Nat.pow_le_pow_right (by decide) (by
    by_contra! hn
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show t ≤ a by omega)
    omega)

private theorem choose_le_of_le_half {n a b : ℕ} (h : a ≤ b) (ht : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, h using Nat.le_induction with
  | base => rfl
  | succ b _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem counts_grow {n r : ℕ} (hn : 256 ≤ n) (hr : 30 ≤ r) (hc : 30 ≤ n - r)
    (hrn : r ≤ n) : 2 ^ 128 < n.choose r := by
  have anchor : 2 ^ 128 < (256 : ℕ).choose 30 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have first := anchor.trans_le (Nat.choose_le_choose 30 hn)
  by_cases hhalf : r ≤ n / 2
  · exact first.trans_le (choose_le_of_le_half hr hhalf)
  · rw [← Nat.choose_symm hrn]
    exact first.trans_le (choose_le_of_le_half hc (by omega))

private theorem binomials_above {n k : ℕ} (hd : ∃ t : ℕ, n = 2 ^ t)
    (hr : hasPrizeRate n k) (hout : ¬ withinCeiling n k) :
    2 ^ 128 < n.choose k ∧ 2 ^ 128 < n.choose (k + 1) := by
  obtain ⟨t, ht⟩ := hd
  have h128 : 128 < n := by unfold withinCeiling at hout; omega
  have h256 : 256 ≤ n := pow2_jump (a := 7) ht h128
  have hk : 32 ≤ k := by
    rcases hr with hr | hr | hr | hr
    · omega
    · omega
    · omega
    · have h' : 256 < n := by unfold withinCeiling at hout; omega
      have : 512 ≤ n := pow2_jump (a := 8) ht h'
      omega
  have hkn : 2 * k ≤ n := by rcases hr with hr | hr | hr | hr <;> omega
  exact ⟨counts_grow h256 (by omega) (by omega) (by omega),
    counts_grow h256 (by omega) (by omega) (by omega)⟩

/-- Over every sponsor-sized field, the joint large-field answers force the sharp length ceiling. -/
theorem necessary [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D] {k m : ℕ} [NeZero m]
    (hr : hasPrizeRate (Fintype.card I) k) (hq : Fintype.card F < 2 ^ 256) (h : joint D k m) :
    withinCeiling (Fintype.card I) k := by
  have hn := Fintype.card_pos (α := I)
  have hk : 0 < k := by rcases hr with h | h | h | h <;> omega
  have c := (JointAdjacentFieldReview.prize_rate_size_iff D hk hr hq).mp h
  by_contra hout
  have high := (binomials_above (ReedSolomon.Smooth.h_card_pow2 (domain := D)) hr hout).1
  have lim := (Nat.mul_le_mul_right (2 ^ 128) (le_max_right
    ((Fintype.card I).choose (k + 1)) ((Fintype.card I).choose k))).trans c
  omega

/-- Above the rate's length ceiling, MCA is already unsafe at `k+1` agreements
and the worst list exceeds budget at `k` agreements, at every positive width. -/
theorem failures_beyond_ceiling [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k m : ℕ} [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hq : Fintype.card F < 2 ^ 256) (hout : ¬ withinCeiling (Fintype.card I) k) :
    (prizeThreshold : ℝ≥0) < epsMCA (F := F) (ReedSolomon.code D k : Set (I → F))
        (1 - ((k + 1 : ℕ) : ℝ≥0) / Fintype.card I) ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
        (Lambda (ListInterpolationBoundary.words D k m)
          (((Fintype.card I - k : ℕ) : ℝ) / Fintype.card I) : ℝ≥0∞) := by
  classical
  have hn := Fintype.card_pos (α := I)
  have hk : 0 < k := by rcases hr with h | h | h | h <;> omega
  have hkn : k < Fintype.card I := by rcases hr with h | h | h | h <;> omega
  obtain ⟨hlist, hmca⟩ := binomials_above (ReedSolomon.Smooth.h_card_pow2 (domain := D)) hr hout
  have low : Fintype.card F / 2 ^ 128 < 2 ^ 128 := by omega
  constructor
  · have hn' : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast hn
    have hrat : ((k + 1 : ℕ) : ℝ≥0) / Fintype.card I ≤ 1 :=
      (div_le_one hn').mpr (by exact_mod_cast hkn)
    rw [epsMCA_eq_epsMCA_one_of_le_succ D k (by
      rw [tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn'.ne', Nat.cast_add, Nat.cast_one])]
    exact lt_of_not_ge fun h => (low.trans hmca).not_ge ((JointAdjacentFieldReview.endpoint_iff
      D hk hkn hq).mp h)
  · apply lt_of_not_ge
    intro good
    have bound := (ListSupportRank.lambda_le_floor_iff (K := F) _ _ _).mp good
    rw [ListInterpolationBoundary.at_dimension_agreement D hk hkn.le (NeZero.pos m)] at bound
    have count : (Fintype.card I).choose k ≤ RankReview.budget F (prizeThreshold : ℝ≥0) := by
      unfold RankReview.budget
      exact_mod_cast bound
    rw [RankExecutable.prizeBudget] at count
    exact (low.trans hlist).not_ge count

private theorem fits_bls {n k : ℕ} (h : withinCeiling n k) :
    max (n.choose (k + 1)) (n.choose k) * 2 ^ 128 ≤ BlsScalarSubgroup.P := by
  rcases h with hn | ⟨hr, hn⟩
  · have bound (t : ℕ) : n.choose t ≤ (128 : ℕ).choose 64 :=
      (Nat.choose_le_choose t hn).trans (Nat.choose_le_middle t 128)
    refine (Nat.mul_le_mul_right _ (max_le (bound _) (bound _))).trans ?_
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  · have hk : k ≤ 16 := by omega
    have bound (t : ℕ) (ht : t ≤ 17) : n.choose t ≤ (256 : ℕ).choose 17 := by
      exact (Nat.choose_le_choose t hn).trans (choose_le_of_le_half ht (by decide))
    refine (Nat.mul_le_mul_right _ (max_le (bound _ (by omega)) (bound _ (by omega)))).trans ?_
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide

/-- One explicit certified field realizes every admissible dyadic length at every positive width. -/
theorem bls_realizes {n k : ℕ} [NeZero n] (hr : hasPrizeRate n k)
    (hd : ∃ t : ℕ, n = 2 ^ t) (h : withinCeiling n k) :
    ∃ D : Fin n ↪ ZMod BlsScalarSubgroup.P, Nonempty (ReedSolomon.Smooth D) ∧
      ∀ m : ℕ, [NeZero m] → joint D k m := by
  obtain ⟨t, ht⟩ := hd
  have hn : n ≤ 256 := by rcases h with h | h <;> omega
  have he : t ≤ 8 := by
    by_contra! ht'
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 9 ≤ t by omega)
    omega
  have dvd : n ∣ BlsScalarSubgroup.P - 1 := by
    rw [ht]
    exact (pow_dvd_pow 2 he).trans (by decide : 2 ^ 8 ∣ BlsScalarSubgroup.P - 1)
  obtain ⟨D, ⟨sm⟩⟩ := SmoothPowerMcaDescent.exists_prime_domain dvd ⟨t, ht⟩
  refine ⟨D, ⟨sm⟩, fun m _ => ?_⟩
  have hp := NeZero.pos n
  have hk : 0 < k := by rcases hr with h | h | h | h <;> omega
  apply (JointAdjacentFieldReview.prize_rate_size_iff D hk (by simpa using hr)
    (by rw [ZMod.card]; decide)).mpr
  simpa only [Fintype.card_fin, ZMod.card] using fits_bls h

set_option exponentiation.threshold 512 in
set_option maxRecDepth 4096 in
private theorem dense_count {n j : ℕ} (hn : 1024 ≤ n) (hj : 128 ≤ j)
    (hc : 128 ≤ n - j) : 2 ^ 512 < n.choose j := by
  have base : 2 ^ 512 < (1024 : ℕ).choose 128 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have bound := base.trans_le (Nat.choose_le_choose 128 hn)
  by_cases half : j ≤ n / 2
  · exact bound.trans_le (choose_le_of_le_half hj half)
  · rw [← Nat.choose_symm (show j ≤ n by omega)]
    exact bound.trans_le (choose_le_of_le_half hc (by omega))

set_option exponentiation.threshold 512 in
omit [DecidableEq F] in
/-- On every injective domain in this range, the worst-pair MCA probability
is one as soon as at most `k+1` agreements are required. The worst list at
`k` agreements contains more than the square of the field order. -/
theorem dense_saturation [Nonempty I] (D : I ↪ F) {k m : ℕ} [NeZero m]
    (hn : 1024 ≤ Fintype.card I) (hk : 128 ≤ k) (hc : 128 ≤ Fintype.card I - (k + 1))
    (hq : Fintype.card F < 2 ^ 256) {δ : ℝ≥0}
    (hδ : 1 - ((k + 1 : ℕ) : ℝ≥0) / Fintype.card I ≤ δ) :
    epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ = 1 ∧
      ((Fintype.card F ^ 2 : ℕ) : ℕ∞) < Lambda (ListInterpolationBoundary.words D k m)
        (((Fintype.card I - k : ℕ) : ℝ) / Fintype.card I) := by
  classical
  have hn' : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hkn : k + 1 ≤ Fintype.card I := by omega
  have field : Fintype.card F ^ 2 < 2 ^ 512 := by
    simpa only [← pow_mul] using Nat.pow_lt_pow_left hq (by decide : 2 ≠ 0)
  let t : ℝ≥0 := 1 - ((k + 1 : ℕ) : ℝ≥0) / Fintype.card I
  have size : (1 - t) * Fintype.card I = (k + 1 : ℕ) := by
    have ratio := (div_le_one hn').mpr (show ((k + 1 : ℕ) : ℝ≥0) ≤ Fintype.card I by
      exact_mod_cast hkn)
    dsimp [t]
    rw [tsub_tsub_cancel_of_le ratio, div_mul_cancel₀ _ hn'.ne']
  constructor
  · rw [epsMCA_interleaved_eq]
    have atStep : epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) t = 1 := by
      let _ : SampleableType F := SampleableType.ofFintype _
      let eqv := (Fintype.equivFin I).symm
      let x := eqv.toEmbedding.trans D
      rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
        eqv x D (fun _ => rfl), epsMCA_eq_mcaError]
      apply BoundaryFullMass.mcaError_eq_one x (by omega)
      · rw [Fintype.card_fin, size]
        exact_mod_cast Nat.lt_succ_self k
      · rw [Fintype.card_fin, size, Nat.cast_add_one]
      · exact (Nat.pow_le_pow_left (Nat.sub_le _ _) 2).trans_lt
          (field.trans (dense_count hn (by omega) hc))
    apply le_antisymm (epsMCA_le_one _ _)
    rw [← atStep]
    exact epsMCA_mono _ hδ
  · rw [ListInterpolationBoundary.at_dimension_agreement D (by omega) (by omega) (NeZero.pos m)]
    exact_mod_cast field.trans (dense_count hn hk (by omega))

omit [DecidableEq F] in
/-- All prize rates satisfy the full-mass test from length 2048, and the top
three rates already satisfy it from length 1024. Smoothness is unnecessary. -/
theorem prize_dense [Nonempty I] (D : I ↪ F) {k m : ℕ} [NeZero m]
    (hr : hasPrizeRate (Fintype.card I) k) (hn : 1024 ≤ Fintype.card I)
    (hsmall : 16 * k = Fintype.card I → 2048 ≤ Fintype.card I)
    (hq : Fintype.card F < 2 ^ 256) {δ : ℝ≥0}
    (hδ : 1 - ((k + 1 : ℕ) : ℝ≥0) / Fintype.card I ≤ δ) :
    epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ = 1 ∧
      ((Fintype.card F ^ 2 : ℕ) : ℕ∞) < Lambda (ListInterpolationBoundary.words D k m)
        (((Fintype.card I - k : ℕ) : ℝ) / Fintype.card I) := by
  apply dense_saturation D hn _ _ hq hδ
  all_goals rcases hr with h | h | h | h <;> omega

end ProximityPrize.JointDyadicCeilings
