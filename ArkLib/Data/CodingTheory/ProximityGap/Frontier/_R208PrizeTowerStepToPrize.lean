/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R208 prize tower step-to-prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R207PrizeTowerStepConsumer

/-!
# R208 (#466): prize-tower normalized budgets all the way to the square-root prize bound

R207 proves the parent `DyadicTailMGFBound` from prize-index child normalized
R189 budgets.  R168 already proves that this tail-MGF residual implies the
standard square-root-log prize inequality once the moment-to-sup bridge is
available.  This file composes the two.

The theorem is intentionally explicit rather than clever: the remaining
non-bookkeeping inputs are exactly the mathematical ones.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R208PrizeTowerStepToPrize

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207PrizeTowerStepConsumer

/-- Prize-tower one-step consumer all the way to the squared sup-norm prize
bound.  The large-index child hypotheses are those of R207, and the final
`hmoment` hypothesis is the already-standard moment representation used by
R168/S11. -/
theorem prize_sq_of_prizeTower_child_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ)
    (Θ : Finset ℝ) (δLeft δRight : ℝ → ℝ)
    (depth : ℕ)
    (BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
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
    (hBudgetRight : BbulkRight + BspikeRight ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (htParent : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  have hTail : DyadicTailMGFBound s parent :=
    dyadicTailMGF_of_prizeTower_child_normalizedBudgets
      s parent left right Θ δLeft δRight depth
      BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight
      hcard hparent hδLeft hstairLeft hTailLeft hBulkLeft hMassLeft
      hFitLeft hBudgetLeft hδRight hstairRight hTailRight hBulkRight
      hMassRight hFitRight hBudgetRight
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ htParent hP hr hrQ
    hTail hmoment

end ArkLib.ProximityGap.Frontier.R208PrizeTowerStepToPrize

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R208PrizeTowerStepToPrize.prize_sq_of_prizeTower_child_normalizedBudgets
