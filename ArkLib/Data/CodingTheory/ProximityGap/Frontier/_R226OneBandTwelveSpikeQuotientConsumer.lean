/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R226 one-band twelve-spike quotient consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223LowBandSurvivalConsumer

/-!
# R226 (#466): one-band quotient tail with twelve quotient spikes

R226 refines the failed R225 half-band `+2` quotient-tail hypothesis.  Exact
sweeps show two obstructions:

* immediately above `1/2`, the quotient survival fraction is too large for
  coefficient `3/5`;
* moderate carriers can have more than two high quotient spikes.

This file records the corrected consumer shape: pay the low band through
`τ = 1` exactly, then consume a quotient tail

```text
#{q in Q : θ <= qSq q} <= (3/5) * |Q| * exp(-θ/2) + 12,  θ > 1.
```

After the quotient-to-raw lift, the raw spike reserve is `12 * |G|`.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R226OneBandTwelveSpikeQuotientConsumer

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The fixed R226 low-band/tail bound: exact low band through `1`, then
`3/5` exponential bulk plus `12 * |G|` raw spikes. -/
def oneBandTwelveSpikeBound (G : Finset F) (θ : ℝ) : ℝ :=
  lowBandBulkSpikesBound (F := F) 1 (3 / 5) (12 * (G.card : ℝ)) θ

/-- Above the one-band split, a quotient survivor contributes at most `|G|`
raw frequencies. -/
def OneBandRawNonzeroTailLeCosetScale {ι : Type*} (ψ : AddChar F ℂ)
    (G : Finset F) (σ : ℝ) (Q : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) : Prop :=
  ∀ θ ∈ Θ, (1 : ℝ) < θ →
    ((((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ)
      ≤ (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ))

/-- A quotient one-band tail with twelve quotient spikes implies the corrected
raw one-band tail. -/
theorem nonzeroNormalizedSqOneBandTail_twelveSpikes_of_quotient
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (hLift : OneBandRawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, (1 : ℝ) < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, (1 : ℝ) < θ →
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 12 * (G.card : ℝ)) :
    ∀ θ ∈ Θ, (1 : ℝ) < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + 12 * (G.card : ℝ) := by
  intro θ hθ habove
  calc
    (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ habove
    _ ≤ (G.card : ℝ) * Bq θ := by
      exact mul_le_mul_of_nonneg_left (hQTailAbove θ hθ habove) (by positivity)
    _ ≤ (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 12 * (G.card : ℝ) :=
      hScaleAbove θ hθ habove

/-- The R226 quotient one-band/twelve-spike certificate feeds the normalized
quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_quotient_oneBand_twelveSpikes
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (hLift : OneBandRawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, (1 : ℝ) < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, (1 : ℝ) < θ →
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 12 * (G.card : ℝ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * oneBandTwelveSpikeBound (F := F) G θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    ψ G Θ δ 1 (3 / 5) (12 * (G.card : ℝ)) hδ hstair
    (nonzeroNormalizedSqOneBandTail_twelveSpikes_of_quotient
      ψ G Q qSq Θ Bq hLift hQTailAbove hScaleAbove)
    hweighted

end

end ArkLib.ProximityGap.Frontier.R226OneBandTwelveSpikeQuotientConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R226OneBandTwelveSpikeQuotientConsumer.nonzeroNormalizedSqOneBandTail_twelveSpikes_of_quotient
#print axioms ArkLib.ProximityGap.Frontier.R226OneBandTwelveSpikeQuotientConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_quotient_oneBand_twelveSpikes
