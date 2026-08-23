/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R203 large-index normalized budgets)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R193SpikeMassBudgetConsumer

/-!
# R203 (#466): large-index-only normalized budget consumer

R202 refuted a naive universal medium-index direct split: some small dyadic
rows have `MGF(1/4) > 2`.  The prize regime is different.  For fixed
`p ≈ n * 2^128`, every lower 2-adic child has an even larger coset index, so
the relevant branch is the large-index branch only.

This file exposes that interface without a small-case fallback.  If the
cardinality/index lower bound is known and the normalized R193 budgets hold in
that large range, then the quarter-MGF residual follows.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer

/-- Large-index normalized-budget consumer.  The lower bound `N ≤ s.card`
is recorded as an explicit hypothesis, matching the prize tower where all
child quotient sizes are enormous. -/
theorem quarterMGF_of_largeIndex_normalizedBudgets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (_hLarge : N ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulk : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikes_normalizedBudgets s t Θ δ
    Cbulk Kspike Bbulk Bspike Mper hδ hstair hTail hBulk hK hMass hFit hBudget

/-- R189 constants, with the live large-index threshold parameter left explicit. -/
theorem quarterMGF_of_largeIndex_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Bbulk Bspike Mper : ℝ)
    (hLarge : N ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_largeIndex_normalizedBudgets s t Θ δ N
    (3 / 5) 2 Bbulk Bspike Mper hLarge hδ hstair hTail hBulk
    (by norm_num) hMass hFit hBudget

/-- Convenience specialization to the empirically safe threshold `1024`. -/
theorem quarterMGF_of_large1024_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike Mper : ℝ)
    (hLarge : 1024 ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_largeIndex_threeFifths_plus_two_normalizedBudgets
    s t Θ δ 1024 Bbulk Bspike Mper hLarge hδ hstair hTail hBulk
    hMass hFit hBudget

end ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets.quarterMGF_of_largeIndex_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets.quarterMGF_of_largeIndex_threeFifths_plus_two_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets.quarterMGF_of_large1024_threeFifths_plus_two_normalizedBudgets
