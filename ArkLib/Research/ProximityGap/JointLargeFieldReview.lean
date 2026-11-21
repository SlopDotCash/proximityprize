/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankKnownDomain
import ArkLib.Research.ProximityGap.RankExecutable
import ArkLib.Research.ProximityGap.RadiusOne
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-! # Both operational thresholds in the large-field range

For any supplied injective domain, the integer budget bounds the number of bad
scalar labels by counting interpolation circuits. Packing agreement subsets gives
two adjacent possibilities for the first failing list radius. At every prize rate
the same explicit counts evaluate the general rank formulas. A central binomial
coefficient gives one field-size test that works at all rates simultaneously.
-/

namespace ProximityPrize.JointLargeFieldReview
open Code ProximityGap CoreDefinitions FullPrizeReview
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]

/-- The first failing error count when the budget covers the packing bound at
one more than dimension-many agreements. -/
def listCount (n k B : ℕ) : ℕ :=
  if n.choose k ≤ B then n - k + 1 else n - k

private theorem budget_lt_card (ε : ℝ≥0) (hε : ε < 1) :
    RankReview.budget F ε < Fintype.card F := by
  apply (Nat.floor_lt (by positivity)).mpr
  exact (mul_lt_mul_of_pos_right hε (by exact_mod_cast Fintype.card_pos (α := F))).trans_eq
    (one_mul _)

/-- For a supplied injective domain the MCA test passes at every radius through
one. At each positive width the list test changes at the stated integer step. -/
theorem classification (D : I ↪ F) (ε : ℝ≥0) (hε : ε < 1) {k m : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card I) [NeZero m]
    (hc : (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε)
    (hp : (Fintype.card I).choose k / (k + 1) ≤ RankReview.budget F ε)
    (δ : ℝ≥0) (hδ : δ ≤ 1) :
    epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤ (ε : ℝ≥0∞) ∧
      ((Lambda (ListInterpolationBoundary.words D k m) (δ : ℝ) : ℝ≥0∞) ≤
        (ε : ℝ≥0∞) * Fintype.card F ↔
        δ < (listCount (Fintype.card I) k (RankReview.budget F ε) : ℝ≥0) / Fintype.card I) := by
  classical
  constructor
  · rw [epsMCA_interleaved_eq, SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
    exact ((epsMCA_mono _ hδ).trans (epsMCA_one_le_choose_div D k)).trans
      (ENNReal.div_le_div_right (by exact_mod_cast hc) _)
  · refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) (δ : ℝ) ε).trans ?_
    refine (ListInterpolationBoundary.good_iff D hk hkn (NeZero.pos m) hp
      (budget_lt_card ε hε) _).trans ?_
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    rfl

variable [DecidableEq F]

/-- Literal values of both support-rank answer functions on all eligible smooth
codes under the two circuit and packing inequalities. -/
theorem rank_answers (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) (hε : ε < 1)
    {k m : ℕ} (hk : 0 < k) [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hc : (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε)
    (hp : (Fintype.card I).choose k / (k + 1) ≤ RankReview.budget F ε) :
    RankReview.mcaAnswer D ε k = none ∧
      (RankReview.listAnswer D ε k m).map Fin.val =
        some (listCount (Fintype.card I) k (RankReview.budget F ε)) := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k ≤ Fintype.card I := by rcases hr with h | h | h | h <;> omega
  let e := listCount (Fintype.card I) k (RankReview.budget F ε)
  have hle : e < Fintype.card I + 1 := by dsimp [e, listCount]; split <;> omega
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain D ε k hr
  constructor
  · apply correctBoundary_unique Fintype.card_pos hM
    intro δ hδ
    simp only [iff_true]
    rw [← epsMCA_eq_mcaError]
    have h := (classification (m := m) D ε hε hk hkn hc hp δ hδ).1
    rwa [epsMCA_interleaved_eq] at h
  · have h : correctBoundary (Fintype.card I) (some ⟨e, hle⟩) (fun δ =>
        (Lambda (ListInterpolationBoundary.words D k m) (δ : ℝ) : ℝ≥0∞) ≤
          (ε : ℝ≥0∞) * Fintype.card F) := by
      intro δ hδ
      exact (classification (m := m) D ε hε hk hkn hc hp δ hδ).2
    exact congrArg (Option.map Fin.val)
      (correctBoundary_unique Fintype.card_pos (hL m (NeZero.pos m)) h)

/-- At arbitrary tolerance below one, covering the two full binomial counts
makes every MCA radius safe and the first list failure the minimum distance. -/
theorem rank_large_field (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) (hε : ε < 1)
    {k m : ℕ} (hk : 0 < k) [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hB : max ((Fintype.card I).choose (k + 1)) ((Fintype.card I).choose k) ≤
      RankReview.budget F ε) :
    RankReview.mcaAnswer D ε k = none ∧
      (RankReview.listAnswer D ε k m).map Fin.val = some (Fintype.card I - k + 1) := by
  obtain ⟨hc, hl⟩ := max_le_iff.mp hB
  simpa only [listCount, ite_eq_left hl] using
    rank_answers (m := m) D ε hε hk hr hc ((Nat.div_le_self _ _).trans hl)

/-- A single dimension-independent large-field criterion at 128-bit tolerance
makes MCA all-safe and the first list failure the minimum distance at all prize rates. -/
theorem prize_large_field (D : I ↪ F) [ReedSolomon.Smooth D] {k m : ℕ} (hk : 0 < k)
    [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hq : (Fintype.card I).choose (Fintype.card I / 2) * 2 ^ 128 ≤ Fintype.card F) :
    RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none ∧
      (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
        some (Fintype.card I - k + 1) := by
  have hb : (Fintype.card I).choose (Fintype.card I / 2) ≤
      RankReview.budget F (prizeThreshold : ℝ≥0) := by
    rw [RankExecutable.prizeBudget]
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)).mpr hq
  exact rank_large_field D (prizeThreshold : ℝ≥0) (by norm_num [prizeThreshold]) hk hr
    ((max_le (Nat.choose_le_middle _ _) (Nat.choose_le_middle _ _)).trans hb)

end ProximityPrize.JointLargeFieldReview
