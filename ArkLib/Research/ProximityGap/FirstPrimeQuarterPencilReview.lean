/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateTwoRichFloor
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitCriterion
import ArkLib.Research.ProximityGap.SecondPrimeRankReview

/-! # The first-prime quarter-rate threshold and the split-pencil criterion -/

namespace ProximityPrize.FirstPrimeQuarterPencilReview

open Code CoreDefinitions FullPrizeReview ProximityGap ProximityGap.GrandChallenges
open MCAThresholdLedger
open ArkLib.ProximityGap.PrizeShapePrimeP30 ArkLib.ProximityGap.Frontier
open P1RateQuarterCanonicalCodeBridge P1RateQuarterScaleArithmetic QuarterSuccessorSplitCriterion
open scoped NNReal ENNReal

local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

local notation "radius" => (447392428 / 1073741824 : ℝ≥0)
local notation "tol" => ((prizeThreshold : ℝ≥0) : ℝ≥0∞)

private theorem tolerance_eq : tol = (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹) := by
  norm_num [prizeThreshold]

private theorem low_budget : (1073741824 : ℝ≥0∞) / Fintype.card (ZMod P) ≤ tol := by
  rw [ZMod.card, tolerance_eq]
  exact PrizeShapeRateHalfBracket.natCast_div_le_inv_of_mul_le (Q := 2 ^ 128)
    (by decide) prime_P.pos (by decide)

private theorem high_budget : tol < (1073741826 : ℝ≥0∞) / Fintype.card (ZMod P) := by
  rw [ZMod.card]
  have hp : (P : ℝ≥0) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  have h : (prizeThreshold : ℝ≥0) < (1073741826 : ℝ≥0) / (P : ℝ≥0) := by
    apply (lt_div_iff₀ (show (0 : ℝ≥0) < (P : ℝ≥0) by exact_mod_cast prime_P.pos)).mpr
    exact_mod_cast (show (prizeThreshold : ℝ) * (P : ℝ) < 1073741826 by
      norm_num [prizeThreshold, ArkLib.ProximityGap.PrizeShapePrimeP30.P])
  have lifted := ENNReal.coe_lt_coe.mpr h
  simpa only [ENNReal.coe_div hp, ENNReal.coe_ofNat, ENNReal.coe_natCast] using lifted

/-- At 447392428 errors on the first designated subgroup the 128-bit target fails exactly
when the split pencil exists. In that case the maximum is 1073741826 bad scalar labels. -/
theorem successor_failure :
    (tol < epsMCA (F := ZMod P) canonicalCode radius ↔ splitPencil canonicalDomain) ∧
      (splitPencil canonicalDomain → epsMCA (F := ZMod P) canonicalCode radius =
        (1073741826 : ℝ≥0∞) / Fintype.card (ZMod P)) := by
  have h := failure_iff (p := P) (by decide) canonicalDomain (Fintype.card_fin _)
    (by rw [ZMod.card]; decide) 1
  dsimp only at h
  rw [epsMCA_interleaved_eq] at h
  constructor
  · constructor
    · intro bad
      exact h.1.mp (low_budget.trans_lt bad)
    · intro pencil
      exact high_budget.trans_eq (h.2 pencil).symm
  · exact h.2

/-- On the actual named domain the quarter-rate 128-bit operational supremum equals
447392428/n exactly when the split pencil exists. The statement holds at every positive width. -/
theorem threshold_iff (m : ℕ) [NeZero m] :
    mcaDeltaStar (F := ZMod P) (canonicalCode ^⋈ (Fin m)) tol = radius ↔
      splitPencil canonicalDomain := by
  rw [mcaDeltaStar_interleaved_eq]
  constructor
  · intro eq
    apply successor_failure.1.mp
    have hb : mcaDeltaStar (F := ZMod P) canonicalCode tol < 1 := by
      rw [eq, div_lt_one (by norm_num)]
      norm_num
    simpa only [eq] using MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one canonicalCode tol hb
  · intro pencil
    have lower := QuarterRateTwoRichFloor.named_bracket.1
    rw [← tolerance_eq] at lower
    exact le_antisymm (mcaDeltaStar_le_of_bad _ _ (successor_failure.1.mpr pencil)) lower

/-- Absence of the pencil makes 447392428 errors safe and puts the operational
supremum at or beyond the next Hamming step. -/
theorem next_grid_of_no_pencil (m : ℕ) [NeZero m] (no : ¬splitPencil canonicalDomain) :
    (447392429 : ℝ≥0) / 1073741824 ≤
      mcaDeltaStar (F := ZMod P) (canonicalCode ^⋈ (Fin m)) tol := by
  rw [mcaDeltaStar_interleaved_eq]
  apply PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (a := 447392429) (by decide) (by decide : 447392429 ≤ N)
  change epsMCA (F := ZMod P) canonicalCode radius ≤ tol
  exact le_of_not_gt (fun bad => no (successor_failure.1.mp bad))

/-- The exact support-rank prediction returns the named count precisely under the same
three-fiber condition on the canonical evaluation set. -/
theorem rank_iff :
    RankReview.mcaAnswer canonicalDomain (prizeThreshold : ℝ≥0) k =
      some ⟨447392428, by rw [Fintype.card_fin]; decide⟩ ↔ splitPencil canonicalDomain := by
  classical
  let _ : SampleableType (ZMod P) := SampleableType.ofFintype _
  let e : Fin (Fintype.card (Fin N) + 1) := ⟨447392428, by rw [Fintype.card_fin]; decide⟩
  have hn : Fintype.card (Fin N) = 1073741824 := Fintype.card_fin _
  have hv : e.val = 447392428 := rfl
  constructor
  · intro he
    apply successor_failure.1.mp
    apply lt_of_not_ge
    intro safe
    have spec := RankReview.mcaAnswer_correct canonicalDomain (prizeThreshold : ℝ≥0) k radius
      (by rw [div_le_one (by norm_num)]; norm_num)
    rw [he] at spec
    change mcaError (AffineLineGenerator (ZMod P)) (ReedSolomon.code canonicalDomain k)
      (radius : ℝ) ≤ tol ↔ radius < (447392428 : ℝ≥0) / Fintype.card (Fin N) at spec
    rw [← epsMCA_eq_mcaError, hn] at spec
    exact (lt_irrefl radius) (spec.mp safe)
  · intro pencil
    have hs := (threshold_iff 1).mpr pencil
    rw [mcaDeltaStar_interleaved_eq] at hs
    apply SecondPrimeRankReview.rankAnswer_of_interior_supremum canonicalDomain
      (prizeThreshold : ℝ≥0) k e (by rw [hv, hn]; decide)
    rw [hv, hn]
    exact hs

/-- Every exhaustive enumeration of field labels gives the same iff for the executable
rank scan, using the literal integer budget of the first designated prime. -/
theorem executable_iff (E : Fin (Fintype.card (Fin N)) ≃ Fin N)
    (labels : List (ZMod P)) (allLabels : ∀ z, z ∈ labels) :
    (RankExecutable.mcaBoundary E labels canonicalDomain k 1073741824).map Fin.val =
      some 447392428 ↔ splitPencil canonicalDomain := by
  let _ : SampleableType (ZMod P) := SampleableType.ofFintype _
  have hb := RankExecutable.prizeBudget (ZMod P)
  rw [ZMod.card] at hb
  have eq := RankExecutable.mcaBoundary_eq E labels allLabels canonicalDomain
    (prizeThreshold : ℝ≥0) k
  rw [hb, show P / 2 ^ 128 = 1073741824 by decide] at eq
  rw [eq, ← rank_iff]
  cases RankReview.mcaAnswer canonicalDomain (prizeThreshold : ℝ≥0) k with
  | none => simp
  | some e => simp [Fin.ext_iff]

end ProximityPrize.FirstPrimeQuarterPencilReview
