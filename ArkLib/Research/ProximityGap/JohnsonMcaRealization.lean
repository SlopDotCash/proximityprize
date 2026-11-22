/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointJohnsonEquality
import ArkLib.Research.ProximityGap.Frontier.JohnsonQuarticMca

/-! # Which smooth prize parameters can realize the MCA cutoff at Johnson? -/

namespace ProximityPrize.JointJohnsonEquality

open FullPrizeReview ProximityGap RankJohnsonComparison JohnsonQuarticMca
open scoped NNReal ENNReal

/-- On the order-sixteen subgroup with floor budget 111, the canonical MCA answer is
twelve errors. The circuit-density bound covers the predecessor. -/
theorem quartic_mca_answer :
    (RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) 2).map Fin.val = some 12 := by
  have B : RankReview.budget K (prizeThreshold : ℝ≥0) = 111 := by
    rw [RankExecutable.prizeBudget, budget]
  apply SixteenMcaJohnson.answer_of_failure domain (Fintype.card_fin 16) _ (by omega)
  apply lt_of_not_ge
  intro safe
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget] at safe
  change _ ≤ (RankReview.budget K (prizeThreshold : ℝ≥0) : ℝ≥0∞) / Fintype.card K at safe
  rw [B] at safe
  have h := lower.trans safe
  rw [ENNReal.div_le_iff (by simp) (ENNReal.natCast_ne_top _),
    ENNReal.div_mul_cancel (by simp) (ENNReal.natCast_ne_top _)] at h
  norm_num at h

/-- The order-sixteen subgroup at the prime with budget 111 witnesses MCA equality. -/
theorem sixteen_mca : realizable 16 2 false := by
  refine ⟨K, Fin 16, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    domain, ⟨smooth⟩, Fintype.card_fin 16, ?_, ?_, by simp⟩
  · rw [ZMod.card]
    decide
  · rw [cutoff, quartic_mca_answer]
    norm_num [Real.sqrt_div]

/-- At the four sponsor rates, a supplied smooth code over a field below the ceiling
can realize MCA equality with Johnson precisely in dimension one or at length sixteen
and dimension two. At sixteen, this requires a different code from a list equality witness. -/
theorem mca_iff {n k : ℕ} (hr : hasPrizeRate n k) :
    realizable n k false ↔ k = 1 ∨ k = 2 ∧ n = 16 := by
  constructor
  · intro ex
    rcases necessary hr ex with one | ⟨two, len, _⟩
    · exact Or.inl one
    · exact Or.inr ⟨two, len⟩
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact dimension_one hr false
    · exact sixteen_mca

end ProximityPrize.JointJohnsonEquality
