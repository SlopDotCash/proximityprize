/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R224 half-band tail consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223LowBandSurvivalConsumer

/-!
# R224 (#466): fixed half-band tail consumer

R224 probes calibrate the R223 low-band split: for scale `2`, paying
thresholds `θ ≤ 1/2` exactly makes the coefficient `3/5` plausible above the
band on large-index exact anchors.  This file names that clean fixed target.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R224HalfBandTailConsumer

open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fixed `τ = 1/2` low-band split bound with the probed `(3/5, 2)` tail
above the band. -/
noncomputable def halfBandThreeFifthsPlusTwoBound (θ : ℝ) : ℝ :=
  lowBandBulkSpikesBound (F := F) (1 / 2) (3 / 5) 2 θ

/-- The calibrated R224 socket: prove the normalized-square survival tail only
for grid thresholds `θ > 1/2`; pay `θ ≤ 1/2` by the full carrier. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_two_tail
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
            Real.exp (-(θ / 2)) + 2)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * halfBandThreeFifthsPlusTwoBound (F := F) θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_threeFifths_plus_two_tail
    ψ G Θ δ (1 / 2) hδ hstair hAboveHalfTail hweighted

end ArkLib.ProximityGap.Frontier.R224HalfBandTailConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R224HalfBandTailConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_halfBand_threeFifths_plus_two_tail
