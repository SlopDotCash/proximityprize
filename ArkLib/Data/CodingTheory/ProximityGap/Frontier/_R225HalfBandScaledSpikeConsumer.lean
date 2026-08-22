/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R225 half-band scaled-spike consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223LowBandSurvivalConsumer

/-!
# R225 (#466): half-band consumer with raw-frequency scaled spikes

R224 fixed the low-band cutoff at `τ = 1/2`, but the literal `+2` spike
reserve is a quotient-carrier statement.  On the raw nonzero-frequency carrier,
a quotient `+2` spike reserve lifts to `+ 2 * |G|`.

This file records the corrected half-band raw-frequency socket.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R225HalfBandScaledSpikeConsumer

open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fixed `τ = 1/2` low-band split bound with quotient-safe raw spike reserve
`2 * |G|`. -/
noncomputable def halfBandThreeFifthsPlusScaledTwoBound (G : Finset F) (θ : ℝ) : ℝ :=
  lowBandBulkSpikesBound (F := F) (1 / 2) (3 / 5) (2 * (G.card : ℝ)) θ

/-- Corrected raw-frequency half-band socket: prove the normalized-square
survival tail only for grid thresholds `θ > 1/2`, with spike reserve
`2 * |G|`; pay `θ ≤ 1/2` by the full carrier. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_scaledTwo_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hAboveHalfTail : ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + 2 * (G.card : ℝ))
    (hweighted :
      (∑ θ ∈ Θ, δ θ * halfBandThreeFifthsPlusScaledTwoBound (F := F) G θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    ψ G Θ δ (1 / 2) (3 / 5) (2 * (G.card : ℝ))
    hδ hstair hAboveHalfTail hweighted

end ArkLib.ProximityGap.Frontier.R225HalfBandScaledSpikeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R225HalfBandScaledSpikeConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_scaledTwo_tail
