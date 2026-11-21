/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.FullPrizeContract
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128

/-! Operational thresholds on the smooth prime-field domain of length 128. -/
set_option autoImplicit false

namespace ProximityPrize.KnownDomainReview
open ProximityGap ProximityGap.GrandChallenges FullPrizeReview FourRateListPrime246
open scoped NNReal ENNReal

noncomputable section

private def errorCount (e : ℕ) (he : e ≤ 128) : Boundary (Fintype.card H) :=
  some ⟨e, by rw [card_H]; omega⟩

/-- At half rate 62 errors first fail MCA. All three smaller rates pass through radius one. -/
def mcaAnswer (k : ℕ) : Boundary (Fintype.card H) :=
  if k = 64 then errorCount 62 (by decide) else none

/-- First list-budget failures at dimensions 64, 32, 16 and 8, independent of positive width. -/
def listAnswer (k _m : ℕ) : Boundary (Fintype.card H) :=
  if k = 64 then errorCount 63 (by decide)
  else if k = 32 then errorCount 97 (by decide)
  else if k = 16 then errorCount 113 (by decide)
  else errorCount 121 (by decide)

/-- For every eligible dimension and positive list width, the explicit answers classify every
real radius in the unit interval at the 128-bit security target. -/
theorem correctForPrime246 :
    correctForDomain domain (prizeThreshold : ℝ≥0) mcaAnswer listAnswer := by
  intro k hk
  have hdim : k = 64 ∨ k = 32 ∨ k = 16 ∨ k = 8 := by
    unfold hasPrizeRate at hk
    rw [card_H] at hk
    omega
  constructor
  · intro δ _
    dsimp only
    rw [← epsMCA_eq_mcaError]
    rcases hdim with rfl | hk
    · simpa [mcaAnswer, errorCount, card_H] using
        FourRateSmoothMca128.half_good_iff domain card_H FourRateSmoothMca128.prime246_window δ
    · have hk' : k ≠ 64 := by omega
      simp only [mcaAnswer, if_neg hk', iff_true]
      exact FourRateSmoothMca128.lower_rates_good domain card_H
        FourRateSmoothMca128.prime246_window hk δ
  · intro m hm δ _
    obtain ⟨j, hj⟩ : ∃ j : Fin 4, k = prizeDimension (ι := H) j := by
      rcases hdim with rfl | rfl | rfl | rfl
      · exact ⟨0, by norm_num [prizeDimension, prizeDenominator, card_H]⟩
      · exact ⟨1, by norm_num [prizeDimension, prizeDenominator, card_H]⟩
      · exact ⟨2, by norm_num [prizeDimension, prizeDenominator, card_H]⟩
      · exact ⟨3, by norm_num [prizeDimension, prizeDenominator, card_H]⟩
    subst k
    refine (FourRateListPrime246.list_threshold j m hm (δ : ℝ)).trans ?_
    fin_cases j <;>
      norm_num [prizeDimension, prizeDenominator, card_H, firstBad, FourRateList128.firstBad,
        listAnswer, errorCount, ← NNReal.coe_lt_coe]
end

#print axioms correctForPrime246
end ProximityPrize.KnownDomainReview
