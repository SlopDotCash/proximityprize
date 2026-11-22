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

/-- On sixteen distinct sites at dimension two, every field either fails MCA by eleven
errors or keeps the interleaved list safe through twelve, at the 128-bit tolerance. -/
theorem separate (D : I ↪ F) (hn : Fintype.card I = 16) (m : ℕ) :
    cutoff (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) 2) ≤ 11 ∨
      12 < cutoff (RankReview.listAnswer D (prizeThreshold : ℝ≥0) 2 m) := by
  classical
  let ε : ℝ≥0 := prizeThreshold
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
    have tiny : RankReview.budget F ε < Fintype.card F := by
      rw [show ε = (prizeThreshold : ℝ≥0) from rfl, RankExecutable.prizeBudget]
      exact Nat.div_lt_self Fintype.card_pos (by decide)
    omega

end ProximityPrize.SixteenJohnsonSeparation
