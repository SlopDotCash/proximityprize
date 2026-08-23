/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R223 low-band survival consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer

/-!
# R223 (#466): low-band split survival consumer

R222 paid only the zero threshold exactly.  R223 generalizes the socket: pay
every grid threshold `θ ≤ τ` by the full carrier, and require the exponential
bulk-plus-spikes tail only above the low band.

This matches the R223 probe, where `τ = 0.5` removes the first positive-bin
tail failure while keeping the R213 quarter-MGF budget below `2 * carrier` on
large-index exact anchors.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer

open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Low-band split bound: full carrier at thresholds `θ ≤ τ`, exponential
bulk-plus-spikes above the band. -/
noncomputable def lowBandBulkSpikesBound (τ Cbulk Kspike : ℝ) (θ : ℝ) : ℝ :=
  if θ ≤ τ then
    ((nonzeroFreqs (F := F)).card : ℝ)
  else
    Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) * Real.exp (-(θ / 2)) + Kspike

/-- A tail estimate above the low band extends to a full grid-tail estimate
when the low band is paid by the carrier. -/
theorem lowBandGridTail_of_above_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (τ Cbulk Kspike : ℝ)
    (hAboveTail : ∀ θ ∈ Θ, τ < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + Kspike) :
    NonzeroNormalizedSqGridTail ψ G σ Θ
      (lowBandBulkSpikesBound (F := F) τ Cbulk Kspike) := by
  intro θ hθ
  by_cases hlow : θ ≤ τ
  · simp only [lowBandBulkSpikesBound, hlow, ↓reduceIte]
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset
        (fun b => θ ≤ ‖eta ψ G b‖ ^ (2 : ℕ) / σ ^ (2 : ℕ))
        (nonzeroFreqs (F := F)))
  · have habove : τ < θ := lt_of_not_ge hlow
    simpa [lowBandBulkSpikesBound, hlow] using hAboveTail θ hθ habove

/-- The low-band split bulk-plus-spikes survival envelope implies the R213
normalized-square quarter-MGF residual once its weighted staircase budget fits
under `2 * carrier`. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (τ Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hAboveTail : ∀ θ ∈ Θ, τ < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + Kspike)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * lowBandBulkSpikesBound (F := F) τ Cbulk Kspike θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
    ψ G Θ δ (lowBandBulkSpikesBound (F := F) τ Cbulk Kspike)
    hδ hstair
    (lowBandGridTail_of_above_tail ψ G Θ τ Cbulk Kspike hAboveTail)
    hweighted

/-- Literal `(τ, 3/5, 2)` specialization. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_threeFifths_plus_two_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (τ : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hAboveTail : ∀ θ ∈ Θ, τ < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + 2)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * lowBandBulkSpikesBound (F := F) τ (3 / 5) 2 θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    ψ G Θ δ τ (3 / 5) 2 hδ hstair hAboveTail hweighted

end ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer.lowBandGridTail_of_above_tail
#print axioms ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
#print axioms ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_threeFifths_plus_two_tail
