/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R201 small-direct / large normalized budgets)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R193SpikeMassBudgetConsumer

/-!
# R201 (#466): small-direct split with normalized large-branch budgets

R197 splits the quarter-MGF residual into finite small-index certificates and a
large-index tail route.  R193 later exposed the large route in normalized form:
bulk is an average threshold budget and spikes are a per-point staircase-mass
budget.

This file combines those two interfaces.  For the live R189 constants, the
large branch now asks for exactly:

* `BulkPlusSpikesGridTail s t Θ (3/5) 2`;
* `NormalizedBulkWeightedBudget Θ δ (3/5) ≤ Bbulk`;
* `StaircaseMass Θ δ ≤ Mper * |s|`;
* `2 * Mper ≤ Bspike`, with `Bbulk + Bspike ≤ 2`.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer

/-- Small-index direct certificates plus normalized large-branch budgets prove
the quarter-MGF residual everywhere. -/
theorem quarterMGF_of_smallDirect_or_largeNormalizedBudgets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s t)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulkLarge : N ≤ s.card → NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMassLarge : N ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  by_cases hs : s.card < N
  · exact hSmall hs
  · have hN : N ≤ s.card := Nat.le_of_not_lt hs
    exact quarterMGF_of_bulkPlusSpikes_normalizedBudgets s t Θ δ
      Cbulk Kspike Bbulk Bspike Mper hδ hstair (hTailLarge hN)
      (hBulkLarge hN) hK (hMassLarge hN) hFit hBudget

/-- The live threshold `N = 32`, with arbitrary bulk/spike constants. -/
theorem quarterMGF_of_small32Direct_or_largeNormalizedBudgets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s t)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hBulkLarge : 32 ≤ s.card → NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMassLarge : 32 ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_smallDirect_or_largeNormalizedBudgets s t Θ δ 32
    Cbulk Kspike Bbulk Bspike Mper hδ hstair hSmall hTailLarge
    hBulkLarge hK hMassLarge hFit hBudget

/-- The R189 constants used by the current spike route. -/
theorem quarterMGF_of_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Bbulk Bspike Mper : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s t)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hBulkLarge : 32 ≤ s.card → NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMassLarge : 32 ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_small32Direct_or_largeNormalizedBudgets s t Θ δ
    (3 / 5) 2 Bbulk Bspike Mper hδ hstair hSmall hTailLarge
    hBulkLarge (by norm_num) hMassLarge hFit hBudget

end ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets.quarterMGF_of_smallDirect_or_largeNormalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets.quarterMGF_of_small32Direct_or_largeNormalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets.quarterMGF_of_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
