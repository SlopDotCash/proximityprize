/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointLargeFieldCriterion
import ArkLib.Research.ProximityGap.Frontier.CircuitBudgetRadius
import ArkLib.Research.ProximityGap.Frontier._MCAReindexThresholdEquiv
import ArkLib.Research.ProximityGap.Frontier._MCAGoodRadiusMaximum

/-! # An adjacent pair of closed rank formulas on the supplied domain

When the budget covers the packing bounds at one additional agreement, the two
answers at 128-bit tolerance each admit an explicit binomial test. The
underlying testing families are interpolation circuits for folded words and
dimension-many agreement subsets for lists.
-/

namespace ProximityPrize.JointAdjacentFieldReview
open Code ProximityGap CoreDefinitions FullPrizeReview
open ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- A covered circuit count makes MCA safe through radius one. Otherwise the
first failure under the adjacent packing bound occurs at `k+1` agreements. -/
def mcaCount (n k B : ℕ) : Option ℕ :=
  if n.choose (k + 1) ≤ B then none else some (n - (k + 1))

private theorem tolerance_eq : ((prizeThreshold : ℝ≥0) : ℝ≥0∞) = 1 / ((2 ^ 128 : ℕ) : ℝ≥0∞) := by
  norm_num [prizeThreshold]

omit [DecidableEq F] in
/-- The scalar circuit criterion below the field-size ceiling, transported to
an arbitrary coordinate type and expressed as a real Hamming boundary. -/
private theorem circuit_step [SampleableType F] (D : I ↪ F) {k : ℕ} (hk : 0 < k)
    (hkn : k < Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hc : (Fintype.card I).choose (k + 1) / (k + 1) ≤ Fintype.card F / 2 ^ 128)
    (hb : Fintype.card F / 2 ^ 128 < (Fintype.card I).choose (k + 1))
    (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤ (prizeThreshold : ℝ≥0) ↔
      δ < ((Fintype.card I - (k + 1) : ℕ) : ℝ≥0) / Fintype.card I := by
  classical
  let e := (Fintype.equivFin I).symm
  let x := e.toEmbedding.trans D
  have h := CircuitBudgetRadius.good_iff (D := 2 ^ 128) x hk hkn (by decide) (by convert hq using 1)
    hc hb δ
  rw [← epsMCA_eq_mcaError] at h ⊢
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e x D (fun _ => rfl),
    tolerance_eq, h]
  have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  simp only [lt_div_iff₀ hn, Nat.cast_tsub, tsub_mul, one_mul, lt_tsub_iff_right]
  rw [add_comm]

/-- Both first failures at every eligible prize rate and width once the integer
budget covers the two one-more-agreement packing bounds. -/
theorem rank_answers (D : I ↪ F) [ReedSolomon.Smooth D] {k m : ℕ} (hk : 0 < k)
    [NeZero m] (hr : hasPrizeRate (Fintype.card I) k) (hq : Fintype.card F < 2 ^ 256)
    (hc : (Fintype.card I).choose (k + 1) / (k + 1) ≤ Fintype.card F / 2 ^ 128)
    (hp : (Fintype.card I).choose k / (k + 1) ≤ Fintype.card F / 2 ^ 128) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val =
        mcaCount (Fintype.card I) k (Fintype.card F / 2 ^ 128) ∧
      (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
        some (JointLargeFieldReview.listCount (Fintype.card I) k (Fintype.card F / 2 ^ 128)) := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k < Fintype.card I := by rcases hr with h | h | h | h <;> omega
  by_cases hb : (Fintype.card I).choose (k + 1) ≤ Fintype.card F / 2 ^ 128
  · have h := JointLargeFieldReview.rank_answers (m := m) D (prizeThreshold : ℝ≥0)
      (by norm_num [prizeThreshold]) hk hr (by rwa [RankExecutable.prizeBudget])
      (by rwa [RankExecutable.prizeBudget])
    rw [RankExecutable.prizeBudget] at h
    exact ⟨by rw [h.1]; simp only [mcaCount, ite_eq_left hb, Option.map_none], h.2⟩
  have ⟨hM, hL⟩ := RankReview.correctForEveryDomain D (prizeThreshold : ℝ≥0) k hr
  let n := Fintype.card I
  let ix : Fin (n + 1) := ⟨n - (k + 1), by omega⟩
  have hM' : correctBoundary n (some ix) (fun δ =>
      mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤
        (prizeThreshold : ℝ≥0)) := by
    intro δ _
    exact circuit_step D hk hkn hq hc (Nat.lt_of_not_ge hb) δ
  let j := JointLargeFieldReview.listCount n k (Fintype.card F / 2 ^ 128)
  have hj : j < n + 1 := by dsimp [j, JointLargeFieldReview.listCount]; split <;> omega
  have hL' : correctBoundary n (some ⟨j, hj⟩) (fun δ =>
      (Lambda (ListInterpolationBoundary.words D k m) (δ : ℝ) : ℝ≥0∞) ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) := by
    intro δ _
    refine (ListInterpolationBoundary.prize_good_iff D hk hkn.le (NeZero.pos m) hp _).trans ?_
    change (_ < _) ↔ δ < (j : ℝ≥0) / n
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    rfl
  refine ⟨?_, congrArg (Option.map Fin.val)
    (correctBoundary_unique Fintype.card_pos (hL m (NeZero.pos m)) hL')⟩
  simpa only [mcaCount, ite_eq_right hb, Option.map_some, ix, n] using
    congrArg (Option.map Fin.val) (correctBoundary_unique Fintype.card_pos hM hM')

omit [DecidableEq F] in
/-- The radius-one crossing on every injective domain in the sponsor field range. -/
theorem endpoint_iff (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (hq : Fintype.card F < 2 ^ 256) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) 1 ≤ (prizeThreshold : ℝ≥0) ↔
      (Fintype.card I).choose (k + 1) ≤ Fintype.card F / 2 ^ 128 := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let e := (Fintype.equivFin I).symm
  let x := e.toEmbedding.trans D
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e x D (fun _ => rfl), tolerance_eq]
  constructor
  · intro good
    have hs : MCAThresholdLedger.mcaDeltaStar (F := F)
        (ReedSolomon.code x k : Set (Fin (Fintype.card I) → F)) (1 / ((2 ^ 128 : ℕ) : ℝ≥0∞)) = 1 :=
      le_antisymm (csSup_le' fun _ ha => ha.1)
        (MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl good)
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)).mpr
    exact (BoundarySecurityBudget.deltaStar_eq_one_iff x hk hkn (by decide : 0 < 2 ^ 128)
      (by convert hq using 1)).mp hs
  · intro hc
    exact (epsMCA_one_le_choose_div x k).trans
      ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2 ^ 128)).mpr
        (by simpa only [Fintype.card_fin] using hc))

omit [DecidableEq F] in
/-- Literal answer to the attained-maximum question. A largest safe real radius exists
exactly in the binomial field-size range, and the only possible value is one. -/
theorem attained_iff (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (hq : Fintype.card F < 2 ^ 256) (δ : ℝ≥0) :
    IsGreatest (MCAThresholdLedger.mcaGoodRadii (F := F) (ReedSolomon.code D k : Set (I → F))
      (prizeThreshold : ℝ≥0)) δ ↔
      δ = 1 ∧ (Fintype.card I).choose (k + 1) ≤ Fintype.card F / 2 ^ 128 := by
  classical
  constructor
  · intro hs
    have h := ProximityGap.Frontier.MCAGoodRadiusMaximum.greatest_good_radius_eq_one _ _ _ hs
    subst δ
    exact ⟨rfl, (endpoint_iff D hk hkn hq).mp hs.1.2⟩
  · rintro ⟨rfl, hc⟩
    exact ⟨⟨le_rfl, (endpoint_iff D hk hkn hq).mpr hc⟩, fun _ hx => hx.1⟩

/-- Below the sponsor field-size ceiling the lack of any failing MCA grid point
is equivalent to covering every detecting circuit with the integer budget. -/
theorem mca_all_safe_iff (D : I ↪ F) [ReedSolomon.Smooth D] {k : ℕ} (hk : 0 < k)
    (hr : hasPrizeRate (Fintype.card I) k) (hq : Fintype.card F < 2 ^ 256) :
    RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none ↔
      (Fintype.card I).choose (k + 1) ≤ Fintype.card F / 2 ^ 128 := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k < Fintype.card I := by rcases hr with h | h | h | h <;> omega
  have hM := (RankReview.correctForEveryDomain D (prizeThreshold : ℝ≥0) k hr).1
  constructor
  · intro hall
    have hone := hM 1 le_rfl
    rw [hall] at hone
    apply (endpoint_iff D hk hkn hq).mp
    rw [epsMCA_eq_mcaError]
    exact hone.mpr trivial
  · intro hc
    apply correctBoundary_unique Fintype.card_pos hM
    intro δ hδ
    simp only [iff_true]
    rw [← epsMCA_eq_mcaError]
    exact (epsMCA_mono _ hδ).trans ((endpoint_iff D hk hkn hq).mpr hc)

/-- An individual eligible rate has all-safe MCA and its list boundary at the
minimum distance exactly when the budget covers both binomial coefficients. -/
theorem prize_rate_size_iff (D : I ↪ F) [ReedSolomon.Smooth D] {k m : ℕ} (hk : 0 < k)
    [NeZero m] (hr : hasPrizeRate (Fintype.card I) k) (hq : Fintype.card F < 2 ^ 256) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none ∧
      (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
        some (Fintype.card I - k + 1)) ↔
    max ((Fintype.card I).choose (k + 1)) ((Fintype.card I).choose k) * 2 ^ 128 ≤
      Fintype.card F := by
  rw [← Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)]
  constructor
  · rintro ⟨hM, hL⟩
    refine max_le ((mca_all_safe_iff D hk hr hq).mp hM) ?_
    rw [← RankExecutable.prizeBudget]
    exact JointLargeFieldCriterion.budget_of_minimum_list D _ hk hr hL
  · intro hB
    apply JointLargeFieldReview.rank_large_field D _ (by norm_num [prizeThreshold]) hk hr
    rwa [RankExecutable.prizeBudget]

end ProximityPrize.JointAdjacentFieldReview
