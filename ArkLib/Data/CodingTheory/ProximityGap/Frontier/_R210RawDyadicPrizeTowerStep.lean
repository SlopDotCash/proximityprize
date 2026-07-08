/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R210 raw dyadic prize-tower step)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R208PrizeTowerStepToPrize
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R209DyadicCauchyNormalization

/-!
# R210 (#466): raw dyadic triangle input to the prize-tower square bound

R208 consumes normalized squared spectra and assumes the abstract pointwise
inequality `parent ≤ left + right`.  R209 proves that this pointwise inequality
follows from the raw dyadic triangle inequality once the parent variance is
doubled.

This file composes the two.  The child budget hypotheses are stated for the
normalized child-square spectra

```text
leftN  i = rawLeft i  ^ 2 / σ^2
rightN i = rawRight i ^ 2 / σ^2
```

and the parent moment bridge is stated for

```text
parentN i = rawParent i ^ 2 / (2 * σ^2).
```
-/

open Finset
open Real

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R210RawDyadicPrizeTowerStep

open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R208PrizeTowerStepToPrize
open ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization

noncomputable section

/-- Raw dyadic triangle plus child large-index normalized budgets imply the
R168/S11 squared prize bound. -/
theorem prize_sq_of_raw_dyadic_prizeTower_child_normalizedBudgets
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
    (hδLeft : ∀ θ ∈ Θ, 0 ≤ δLeft θ)
    (hstairLeft : ∀ b ∈ s,
      Real.exp ((1 / 4 : ℝ) * (rawLeft b ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ rawLeft b ^ 2 / σ ^ 2), δLeft θ)
    (hTailLeft :
      BulkPlusSpikesGridTail s (fun b => rawLeft b ^ 2 / σ ^ 2) Θ (3 / 5) 2)
    (hBulkLeft : NormalizedBulkWeightedBudget Θ δLeft (3 / 5) ≤ BbulkLeft)
    (hMassLeft : StaircaseMass Θ δLeft ≤ MperLeft * (s.card : ℝ))
    (hFitLeft : 2 * MperLeft ≤ BspikeLeft)
    (hBudgetLeft : BbulkLeft + BspikeLeft ≤ 2)
    (hδRight : ∀ θ ∈ Θ, 0 ≤ δRight θ)
    (hstairRight : ∀ b ∈ s,
      Real.exp ((1 / 4 : ℝ) * (rawRight b ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ rawRight b ^ 2 / σ ^ 2), δRight θ)
    (hTailRight :
      BulkPlusSpikesGridTail s (fun b => rawRight b ^ 2 / σ ^ 2) Θ (3 / 5) 2)
    (hBulkRight : NormalizedBulkWeightedBudget Θ δRight (3 / 5) ≤ BbulkRight)
    (hMassRight : StaircaseMass Θ δRight ≤ MperRight * (s.card : ℝ))
    (hFitRight : 2 * MperRight ≤ BspikeRight)
    (hBudgetRight : BbulkRight + BspikeRight ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ s, (rawParent b ^ 2 / (2 * σ ^ 2)) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  let parentN : ι → ℝ := fun b => rawParent b ^ 2 / (2 * σ ^ 2)
  let leftN : ι → ℝ := fun b => rawLeft b ^ 2 / σ ^ 2
  let rightN : ι → ℝ := fun b => rawRight b ^ 2 / σ ^ 2
  have hparentN : ∀ i ∈ s, parentN i ≤ leftN i + rightN i := by
    intro i hi
    exact normalized_parent_sq_le_child_sq_sum hσ
      (hrawParentNonneg i hi) (hrawTriangle i hi)
  have htParent : ∀ b ∈ s, 0 ≤ parentN b := by
    intro b _
    unfold parentN
    positivity
  exact prize_sq_of_prizeTower_child_normalizedBudgets
    s parentN leftN rightN Θ δLeft δRight depth
    BbulkLeft BspikeLeft MperLeft BbulkRight BspikeRight MperRight
    hcard hparentN hδLeft hstairLeft hTailLeft hBulkLeft hMassLeft
    hFitLeft hBudgetLeft hδRight hstairRight hTailRight hBulkRight
    hMassRight hFitRight hBudgetRight hMmax hn hQ htParent hP hr hrQ
    hmoment

end

end ArkLib.ProximityGap.Frontier.R210RawDyadicPrizeTowerStep

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R210RawDyadicPrizeTowerStep.prize_sq_of_raw_dyadic_prizeTower_child_normalizedBudgets
