/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointAdjacentFieldReview
import ArkLib.Research.ProximityGap.Frontier.BlsScalarSubgroup
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

end ProximityPrize.JointDyadicCeilings
