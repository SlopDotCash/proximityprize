/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JohnsonPrimePowerDomain
import ArkLib.Research.ProximityGap.Frontier.JohnsonGridWitness
import ArkLib.Research.ProximityGap.Frontier.SixteenFiveListCap

/-! # A smooth rate-one-eighth code attaining the finite Johnson list boundary

At dimension two over `GF(17^32)`, the tolerance `2^-128` permits six words.
The grid construction gives eight words at twelve errors, while every ball at
a smaller radius has at most six, at every positive interleaving width.
-/

namespace ProximityPrize.JohnsonPrimePowerList

open Code ProximityGap JohnsonPrimePowerDomain
open scoped NNReal ENNReal

/-- The 128-bit list predicate on the supplied field holds precisely at radii below 12/16. -/
theorem good_iff (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    (Lambda (ListInterpolationBoundary.words domain 2 m) (δ : ℝ) : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F ↔ δ < 12 / 16 := by
  let C : Set (Grid → Fin m → F) := ListInterpolationBoundary.words domain 2 m
  refine (ListSupportRank.lambda_le_floor_iff (K := F) C (δ : ℝ) (prizeThreshold : ℝ≥0)).trans ?_
  change Lambda C (δ : ℝ) ≤ (RankReview.budget F (prizeThreshold : ℝ≥0) : ℕ∞) ↔ _
  rw [budget]
  constructor
  · intro safe
    apply lt_of_not_ge
    intro crossed
    have above := JohnsonGridWitness.eight_le_of_coordinates (Fin m) domain coordinates
    have monotone := Lambda_mono (C := C)
      (by exact_mod_cast crossed : (12 / 16 : ℝ) ≤ δ)
    exact (by decide : ¬ (8 : ℕ∞) ≤ 6) (above.trans (monotone.trans safe))
  · intro small
    exact SixteenFiveListCap.list_bound_below domain card_grid m _ (by exact_mod_cast small)

/-- The rank formula yields twelve as the first failing list count for every positive width. -/
theorem list_answer (m : ℕ) [NeZero m] :
    (RankReview.listAnswer domain (prizeThreshold : ℝ≥0) 2 m).map Fin.val = some 12 := by
  let e : Fin (Fintype.card Grid + 1) := ⟨12, by rw [card_grid]; decide⟩
  have correct := RankReview.listAnswer_correct domain (prizeThreshold : ℝ≥0) 2 m
    (by rw [card_grid]; decide)
  have known : FullPrizeReview.correctBoundary (Fintype.card Grid) (some e) (fun δ =>
      (Lambda (ListInterpolationBoundary.words domain 2 m) (δ : ℝ) : ℝ≥0∞) ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) := by
    intro δ _
    change _ ↔ δ < (12 : ℝ≥0) / Fintype.card Grid
    rw [card_grid]
    exact good_iff m δ
  rw [FullPrizeReview.correctBoundary_unique Fintype.card_pos correct known]
  rfl

end ProximityPrize.JohnsonPrimePowerList
