/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R210 nonzero bulk-plus-spikes MGF consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R190BulkPlusSpikesQuarterMGF
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R209NonzeroQuarterMGFResidualConsumer

/-!
# R210 (#466): nonzero bulk-plus-spikes consumer for the quarter-MGF residual

R209 named the remaining analytic input as the nonprincipal quarter-MGF residual

```text
MGFBound (b ≠ 0) (fun b => ‖η_G(b)‖) 2 (1/4).
```

R190 already proves that such a quarter-MGF bound follows from a finite
threshold-grid staircase and a bulk-plus-spikes survival envelope.  This file
specializes R190 to the nonzero Gauss-period spectrum, so the analytic target
is now stated directly as nonprincipal survival-count estimates.
-/

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R210NonzeroBulkPlusSpikesMGFConsumer

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Arbitrary-constant nonzero bulk-plus-spikes route to the named nonprincipal
quarter-MGF residual. -/
theorem nonzeroQuarterMGFResidual_of_bulkPlusSpikesGridTail
    (ψ : AddChar F ℂ) (G : Finset F) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖), δ θ)
    (hTail : BulkPlusSpikesGridTail (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖) Θ Cbulk Kspike)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroQuarterMGFResidual ψ G := by
  exact quarterMGF_of_bulkPlusSpikesGridTail
    (nonzeroFreqs (F := F)) (fun b => ‖eta ψ G b‖) Θ δ Cbulk Kspike
    hδ hstair hTail hweighted

/-- Live `(3/5, 2)` nonzero bulk-plus-spikes route to the named nonprincipal
quarter-MGF residual. -/
theorem nonzeroQuarterMGFResidual_of_threeFifths_plus_two_gridTail
    (ψ : AddChar F ℂ) (G : Finset F) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖), δ θ)
    (hTail : BulkPlusSpikesGridTail (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖) Θ (3 / 5) 2)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroQuarterMGFResidual ψ G := by
  exact nonzeroQuarterMGFResidual_of_bulkPlusSpikesGridTail ψ G Θ δ
    (3 / 5) 2 hδ hstair hTail hweighted

end ArkLib.ProximityGap.Frontier.R210NonzeroBulkPlusSpikesMGFConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R210NonzeroBulkPlusSpikesMGFConsumer.nonzeroQuarterMGFResidual_of_bulkPlusSpikesGridTail
#print axioms ArkLib.ProximityGap.Frontier.R210NonzeroBulkPlusSpikesMGFConsumer.nonzeroQuarterMGFResidual_of_threeFifths_plus_two_gridTail
