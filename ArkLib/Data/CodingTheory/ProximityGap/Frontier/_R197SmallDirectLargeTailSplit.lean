/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R197 small-direct / large-tail split)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R190BulkPlusSpikesQuarterMGF

/-!
# R197 (#466): split small-index direct certificates from the large-index tail route

R196 showed that the R189/R194 spike route is a large-index strategy: tiny
coset counts can make the envelope budget coarse even though the direct
quarter-MGF bound is easy.  This file packages the case split:

* if `s.card < N`, use a finite direct `DyadicQuarterMGFBound` certificate;
* if `N ≤ s.card`, use the R190 bulk-plus-spikes grid-tail route.

For the live proof strategy, instantiate `N = 32`.
-/

set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R197SmallDirectLargeTailSplit

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF

/-- **Small-direct / large-tail split.**  A finite direct certificate below
cardinality threshold `N`, together with the R190 tail certificates above it,
proves the named quarter-MGF residual everywhere. -/
theorem quarterMGF_of_smallDirect_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s t)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hWeightedLarge : N ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicQuarterMGFBound s t := by
  by_cases hs : s.card < N
  · exact hSmall hs
  · have hN : N ≤ s.card := Nat.le_of_not_lt hs
    exact quarterMGF_of_bulkPlusSpikesGridTail s t Θ δ Cbulk Kspike
      hδ hstair (hTailLarge hN) (hWeightedLarge hN)

/-- The live R196 split threshold, specialized at `N = 32`. -/
theorem quarterMGF_of_small32Direct_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s t)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hWeightedLarge : 32 ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_smallDirect_or_largeGridTail s t Θ δ 32 Cbulk Kspike
    hδ hstair hSmall hTailLarge hWeightedLarge

end ArkLib.ProximityGap.Frontier.R197SmallDirectLargeTailSplit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R197SmallDirectLargeTailSplit.quarterMGF_of_smallDirect_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R197SmallDirectLargeTailSplit.quarterMGF_of_small32Direct_or_largeGridTail
