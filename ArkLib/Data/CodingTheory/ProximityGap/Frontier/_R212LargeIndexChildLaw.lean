/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R212 large-index child law)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R210RawDyadicPrizeTowerStep

/-!
# R212 (#466): name the remaining large-index child law

R210 has reduced one prize-tower step to raw dyadic triangle control plus the
large-index normalized R189 budget hypotheses for both children.  This file
bundles those child hypotheses into a single Lean-facing law.  It is the
current mathematical target for the concentration route:

```text
LargeIndexNormalizedChildLaw s t Θ δ Bbulk Bspike Mper
```

means:

* the staircase increments are nonnegative;
* the staircase dominates `exp(t/4)`;
* the R189 bulk-plus-two tail law holds;
* the normalized bulk budget is at most `Bbulk`;
* the staircase mass is at most `Mper |s|`;
* `2*Mper <= Bspike`;
* `Bbulk + Bspike <= 2`.

No analytic estimate is proved here.  The point is to make the final residual
small, named, and attackable.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R212LargeIndexChildLaw

open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R210RawDyadicPrizeTowerStep

noncomputable section

/-- Bundled large-index R189 child law.  This is the residual that the
large-index Gauss-period concentration proof should discharge for a normalized
child spectrum `t`. -/
structure LargeIndexNormalizedChildLaw {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike Mper : ℝ) : Prop where
  nonneg : ∀ θ ∈ Θ, 0 ≤ δ θ
  staircase : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
    ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ
  tail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2
  bulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk
  mass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ)
  fit : 2 * Mper ≤ Bspike
  budget : Bbulk + Bspike ≤ 2

/-- Raw dyadic prize-tower step, with the two child concentration residuals
bundled as `LargeIndexNormalizedChildLaw`. -/
theorem prize_sq_of_raw_dyadic_prizeTower_child_laws
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (rawParent rawLeft rawRight : ι → ℝ) {σ : ℝ}
    (Θ : Finset ℝ) (δLeft δRight : ℝ → ℝ)
    (depth : ℕ)
    (BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hσ : 0 < σ)
    (hcard : s.card = DyadicTowerIndex PrizeTopIndex depth)
    (hrawParentNonneg : ∀ i ∈ s, 0 ≤ rawParent i)
    (hrawTriangle : ∀ i ∈ s, rawParent i ≤ rawLeft i + rawRight i)
    (hLeftLaw :
      LargeIndexNormalizedChildLaw s (fun b => rawLeft b ^ 2 / σ ^ 2)
        Θ δLeft BbulkLeft BspikeLeft MperLeft)
    (hRightLaw :
      LargeIndexNormalizedChildLaw s (fun b => rawRight b ^ 2 / σ ^ 2)
        Θ δRight BbulkRight BspikeRight MperRight)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ s, (rawParent b ^ 2 / (2 * σ ^ 2)) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_raw_dyadic_prizeTower_child_normalizedBudgets
    s rawParent rawLeft rawRight Θ δLeft δRight depth
    BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight
    hσ hcard hrawParentNonneg hrawTriangle
    hLeftLaw.nonneg hLeftLaw.staircase hLeftLaw.tail hLeftLaw.bulk
    hLeftLaw.mass hLeftLaw.fit hLeftLaw.budget
    hRightLaw.nonneg hRightLaw.staircase hRightLaw.tail hRightLaw.bulk
    hRightLaw.mass hRightLaw.fit hRightLaw.budget
    hMmax hn hQ hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R212LargeIndexChildLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R212LargeIndexChildLaw.prize_sq_of_raw_dyadic_prizeTower_child_laws
