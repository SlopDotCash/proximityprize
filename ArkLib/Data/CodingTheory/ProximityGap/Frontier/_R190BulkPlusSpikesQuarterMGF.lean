/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R190 bulk-plus-spikes quarter-MGF consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer

/-!
# R190 (#466): bulk-plus-spikes tail consumer for the quarter-MGF residual

R189 found a sharper empirical route to the child-side residual
`DyadicQuarterMGFBound`:

```text
  N(T) ≤ (3/5) M exp(-T/2) + 2.
```

This file turns that into a reusable Lean-facing consumer.  On any finite
threshold grid `Θ`, if a staircase dominates `exp(t/4)`, each survival count
is bounded by the bulk-plus-spikes envelope, and the weighted envelope budget
is at most `2 |s|`, then the R188 quarter-MGF residual follows.

Status: concentration consumer only.  Residual = prove the bulk-plus-spikes
survival law for actual dyadic Gauss-period spectra and discharge the finite
numerical grid budget.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer

/-- **Bulk-plus-spikes grid tail residual.**  On the threshold grid `Θ`, every
survival count is bounded by
`Cbulk * |s| * exp(-θ/2) + Kspike`.  R189's clean empirical constants are
`Cbulk = 3/5` and `Kspike = 2`. -/
def BulkPlusSpikesGridTail {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (Θ : Finset ℝ) (Cbulk Kspike : ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤
      Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike

/-- **R190 quarter-MGF consumer.**  A bulk-plus-spikes survival envelope on a
staircase grid proves the named quarter-MGF residual once the weighted envelope
budget is below `2 |s|`. -/
theorem quarterMGF_of_bulkPlusSpikesGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ Cbulk Kspike)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicQuarterMGFBound s t := by
  unfold DyadicQuarterMGFBound
  refine mgfBound_of_survival_count_ceiling s t Θ δ
    (fun θ => Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike)
    hδ hstair ?_ hweighted
  intro θ hθ
  exact hTail θ hθ

/-- The R189 constants packaged explicitly: `(3/5)` bulk and two spike cosets. -/
theorem quarterMGF_of_threeFifths_plus_two_gridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : BulkPlusSpikesGridTail s t Θ (3 / 5) 2)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * (s.card : ℝ) * Real.exp (-(θ / 2)) + 2))
        ≤ 2 * (s.card : ℝ)) :
    DyadicQuarterMGFBound s t := by
  exact quarterMGF_of_bulkPlusSpikesGridTail s t Θ δ (3 / 5) 2
    hδ hstair hTail hweighted

end ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF.quarterMGF_of_bulkPlusSpikesGridTail
#print axioms ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF.quarterMGF_of_threeFifths_plus_two_gridTail
