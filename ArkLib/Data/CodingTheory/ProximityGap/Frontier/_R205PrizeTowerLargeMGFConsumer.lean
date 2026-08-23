/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R205 prize tower large-MGF consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R203LargeIndexNormalizedBudgets
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R204PrizeTowerLargeIndex

/-!
# R205 (#466): prize-tower large-index MGF consumer

R203 consumes normalized large-index bulk/spike budgets.  R204 proves that every
dyadic child of the prize quotient-index tower has index at least `1024`.
This file combines them: if a spectrum family has cardinality equal to the
prize tower index at some depth, the R189 normalized budget hypotheses imply
`DyadicQuarterMGFBound` directly.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R205PrizeTowerLargeMGFConsumer

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex

/-- Prize-tower specialization of the R203 large-index normalized-budget route. -/
theorem quarterMGF_of_prizeTowerIndex_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (depth : ℕ) (Bbulk Bspike Mper : ℝ)
    (hcard : s.card = DyadicTowerIndex PrizeTopIndex depth)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  have hLarge : 1024 ≤ s.card := by
    rw [hcard]
    exact large1024_le_prizeTowerIndex depth
  exact quarterMGF_of_large1024_threeFifths_plus_two_normalizedBudgets
    s t Θ δ Bbulk Bspike Mper hLarge hδ hstair hTail hBulk
    hMass hFit hBudget

end ArkLib.ProximityGap.Frontier.R205PrizeTowerLargeMGFConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R205PrizeTowerLargeMGFConsumer.quarterMGF_of_prizeTowerIndex_threeFifths_plus_two_normalizedBudgets
