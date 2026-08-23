/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R207 prize tower step consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R205PrizeTowerLargeMGFConsumer

/-!
# R207 (#466): prize-tower child budgets imply the parent tail-MGF step

R205 proves the quarter-MGF residual for a child spectrum whose coset count is
the prize tower index, assuming the large-index R189 normalized budgets.
R188 proves that two child quarter-MGF bounds imply the parent R168 tail-MGF
bound under the pointwise dyadic parent inequality.

This file combines the two.  It is the current Lean-facing shape of one
prize-tower descent step.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R207PrizeTowerStepConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R205PrizeTowerLargeMGFConsumer

/-- One prize-tower dyadic step.  If both child spectra live at the prize tower
index and satisfy the R189 normalized large-index budget hypotheses, then the
parent spectrum satisfies the R168 tail-MGF bound. -/
theorem dyadicTailMGF_of_prizeTower_child_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ)
    (Θ : Finset ℝ) (δLeft δRight : ℝ → ℝ)
    (depth : ℕ)
    (BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight : ℝ)
    (hcard : s.card = DyadicTowerIndex PrizeTopIndex depth)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hδLeft : ∀ θ ∈ Θ, 0 ≤ δLeft θ)
    (hstairLeft : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δLeft θ)
    (hTailLeft : BulkPlusSpikesGridTail s left Θ (3 / 5) 2)
    (hBulkLeft : NormalizedBulkWeightedBudget Θ δLeft (3 / 5) ≤ BbulkLeft)
    (hMassLeft : StaircaseMass Θ δLeft ≤ MperLeft * (s.card : ℝ))
    (hFitLeft : 2 * MperLeft ≤ BspikeLeft)
    (hBudgetLeft : BbulkLeft + BspikeLeft ≤ 2)
    (hδRight : ∀ θ ∈ Θ, 0 ≤ δRight θ)
    (hstairRight : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * right b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ right b), δRight θ)
    (hTailRight : BulkPlusSpikesGridTail s right Θ (3 / 5) 2)
    (hBulkRight : NormalizedBulkWeightedBudget Θ δRight (3 / 5) ≤ BbulkRight)
    (hMassRight : StaircaseMass Θ δRight ≤ MperRight * (s.card : ℝ))
    (hFitRight : 2 * MperRight ≤ BspikeRight)
    (hBudgetRight : BbulkRight + BspikeRight ≤ 2) :
    DyadicTailMGFBound s parent := by
  have hLeft : DyadicQuarterMGFBound s left :=
    quarterMGF_of_prizeTowerIndex_threeFifths_plus_two_normalizedBudgets
      s left Θ δLeft depth BbulkLeft BspikeLeft MperLeft hcard hδLeft
      hstairLeft hTailLeft hBulkLeft hMassLeft hFitLeft hBudgetLeft
  have hRight : DyadicQuarterMGFBound s right :=
    quarterMGF_of_prizeTowerIndex_threeFifths_plus_two_normalizedBudgets
      s right Θ δRight depth BbulkRight BspikeRight MperRight hcard hδRight
      hstairRight hTailRight hBulkRight hMassRight hFitRight hBudgetRight
  exact dyadicTailMGF_of_child_quarterMGF s parent left right hparent hLeft hRight

end ArkLib.ProximityGap.Frontier.R207PrizeTowerStepConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R207PrizeTowerStepConsumer.dyadicTailMGF_of_prizeTower_child_normalizedBudgets
