/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R225 half-band quotient-tail consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223LowBandSurvivalConsumer

/-!
# R225 (#466): quotient half-band tail to corrected raw half-band MGF

This file combines an abstract quotient-tail interface with the corrected
half-band scaled-spike consumer.  The analytic input is now quotient-sized:

```text
#{quotient orbits : θ <= qSq} <= (3/5) * |Q| * exp(-θ/2) + 2,  θ > 1/2.
```

The raw-frequency conclusion uses the scaled spike reserve `2 * |G|`.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R225HalfBandQuotientTailConsumer

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Fixed `τ = 1/2` low-band split bound with quotient-safe raw spike reserve
`2 * |G|`.  Duplicated here to avoid an olean dependency during fast
iteration; it is definitionally the same expression as the R225 scaled-spike
consumer. -/
def halfBandScaledTwoBound (G : Finset F) (θ : ℝ) : ℝ :=
  lowBandBulkSpikesBound (F := F) (1 / 2) (3 / 5) (2 * (G.card : ℝ)) θ

/-- The local half-band quotient-to-raw counting lift hypothesis: above the
half-band, every quotient survivor contributes at most `|G|` raw frequencies. -/
def HalfBandRawNonzeroTailLeCosetScale {ι : Type*} (ψ : AddChar F ℂ)
    (G : Finset F) (σ : ℝ) (Q : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) : Prop :=
  ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
    ((((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ)
      ≤ (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ))

/-- Quotient tail plus raw-to-quotient counting lift gives the corrected raw
half-band tail envelope with spike reserve `2 * |G|`. -/
theorem nonzeroNormalizedSqHalfBandTail_scaledTwo_of_quotient
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (hLift : HalfBandRawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)) :
    ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + 2 * (G.card : ℝ) := by
  intro θ hθ habove
  calc
    (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ habove
    _ ≤ (G.card : ℝ) * Bq θ := by
      exact mul_le_mul_of_nonneg_left (hQTailAbove θ hθ habove) (by positivity)
    _ ≤ (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ) :=
      hScaleAbove θ hθ habove

/-- Quotient half-band tail certificate feeds the corrected raw half-band
quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_quotient_halfBand_tail
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (hLift : HalfBandRawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, (1 / 2 : ℝ) < θ →
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * halfBandScaledTwoBound (F := F) G θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    ψ G Θ δ (1 / 2) (3 / 5) (2 * (G.card : ℝ)) hδ hstair
    (nonzeroNormalizedSqHalfBandTail_scaledTwo_of_quotient
      ψ G Q qSq Θ Bq hLift hQTailAbove hScaleAbove)
    hweighted

end

end ArkLib.ProximityGap.Frontier.R225HalfBandQuotientTailConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R225HalfBandQuotientTailConsumer.nonzeroNormalizedSqHalfBandTail_scaledTwo_of_quotient
#print axioms ArkLib.ProximityGap.Frontier.R225HalfBandQuotientTailConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_quotient_halfBand_tail
