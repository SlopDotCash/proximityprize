/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JohnsonPrimePowerList
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.Frontier.UniversalTwoHeadBudget
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking

/-! # The two closed tests cannot both first fail at Johnson on sixteen sites

At four agreements, pair packing bounds any dimension-two list by twenty.
At five agreements, two affine heads can produce up to twenty-four bad scalars.
The two opposite tests exclude simultaneous equality for every supplied field.
-/

namespace ProximityPrize.SixteenJohnsonSeparation

open Code FullPrizeReview ProximityGap ProximityGap.MCAThresholdLedger RankJohnsonComparison
open scoped NNReal ENNReal

/-- An interior grid point is safe precisely when its index precedes the operational cutoff.
This includes the all-safe answer. -/
theorem safe_grid_iff {n e : ℕ} {a : Boundary n} {safe : ℝ≥0 → Prop}
    (spec : correctBoundary n a safe) (he : e < n) :
    safe ((e : ℝ≥0) / n) ↔ e < cutoff a := by
  have pos : (0 : ℝ≥0) < n := by exact_mod_cast (show 0 < n by omega)
  have unit : (e : ℝ≥0) / n ≤ 1 := (div_le_one pos).mpr (by exact_mod_cast he.le)
  cases a with
  | none => exact iff_of_true ((spec _ unit).mpr trivial) he
  | some i =>
    refine (spec _ unit).trans ?_
    change (e : ℝ≥0) / n < (i.val : ℝ≥0) / n ↔ e < i.val
    rw [div_lt_div_iff_of_pos_right pos, Nat.cast_lt]

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]

omit [Nonempty I] in
/-- If the integer tolerance covers the whole field, no oversized family of bad
scalars can exist and the MCA answer is all-safe in every dimension. -/
theorem all_safe_of_field_budget (D : I ↪ F) (ε : ℝ≥0) (k : ℕ)
    (full : Fintype.card F ≤ RankReview.budget F ε) : RankReview.mcaAnswer D ε k = none := by
  apply (RankBoundary.firstFailure_eq_none_iff _).mpr
  rintro e ⟨G, count, _⟩
  have bound := Finset.card_le_univ G
  omega

/-- When the integer budget is smaller than the field, either MCA has failed
by eleven errors or the interleaved list remains safe through twelve. -/
theorem separate_of_budget_lt (D : I ↪ F) (hn : Fintype.card I = 16) (ε : ℝ≥0) (m : ℕ)
    (tiny : RankReview.budget F ε < Fintype.card F) :
    cutoff (RankReview.mcaAnswer D ε 2) ≤ 11 ∨
      12 < cutoff (RankReview.listAnswer D ε 2 m) := by
  classical
  by_cases budget : 20 ≤ RankReview.budget F ε
  · right
    have spec := RankReview.listAnswer_correct D ε 2 m (by omega)
    apply (safe_grid_iff spec (show 12 < Fintype.card I by omega)).mp
    apply (ListSupportRank.lambda_le_floor_iff (K := F) _ _ ε).mpr
    change _ ≤ (RankReview.budget F ε : ℕ∞)
    have bound := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D 2 4 m
      (((12 : ℝ≥0) / Fintype.card I : ℝ≥0) : ℝ) (by decide) (by rw [hn]; norm_num)
    have value : (Fintype.card I).choose 2 / (4 : ℕ).choose 2 = 20 := by rw [hn]; decide
    rw [value] at bound
    exact bound.trans (show (20 : ℕ∞) ≤ (RankReview.budget F ε : ℕ∞) by exact_mod_cast budget)
  · left
    let _ : SampleableType F := SampleableType.ofFintype _
    have spec := RankReview.mcaAnswer_correct D ε 2
    apply le_of_not_gt
    intro late
    have safe := (safe_grid_iff spec (show 11 < Fintype.card I by omega)).mpr late
    rw [← epsMCA_eq_mcaError, SimultaneousSupportRank.epsMCA_le_iff_floor_budget] at safe
    change _ ≤ (RankReview.budget F ε : ℝ≥0∞) / Fintype.card F at safe
    have lower := UniversalTwoHeadBudget.mass D (k := 2) (e := 11) (by decide)
      (by omega) (by omega)
    have combined := lower.trans safe
    rw [ENNReal.div_le_iff (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _),
      ENNReal.div_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)]
      at combined
    have natural : min (Fintype.card F) 24 ≤ RankReview.budget F ε := by exact_mod_cast combined
    omega

/-- The 128-bit tolerance always has an integer budget smaller than the field. -/
theorem separate (D : I ↪ F) (hn : Fintype.card I = 16) (m : ℕ) :
    cutoff (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) 2) ≤ 11 ∨
      12 < cutoff (RankReview.listAnswer D (prizeThreshold : ℝ≥0) 2 m) := by
  apply separate_of_budget_lt D hn
  rw [RankExecutable.prizeBudget]
  exact Nat.div_lt_self Fintype.card_pos (by decide)

end ProximityPrize.SixteenJohnsonSeparation
