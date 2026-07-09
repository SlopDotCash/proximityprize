/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R230 parameterized low-band quotient MGF endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R225GaussOrbitTailLift
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223LowBandSurvivalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R229ParamQuotientEnvelopePrizeEndpoint

/-!
# R230 (#466): parameterized low-band quotient tails to MGF

R228/R226 show that the viable quotient survival law is not a universal
all-threshold `(3/5, 2)` envelope.  The sharper shape is:

* pay a low band `θ ≤ τ` by the full carrier;
* prove an exponential quotient tail only for `τ < θ`;
* keep the quotient constants parameterized.

This file packages that residual in Lean.  It is the low-band analogue of R229,
ending at the normalized-square quarter-MGF residual consumed by the prize
endpoint stack.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

namespace ArkLib.ProximityGap.Frontier.R230ParamLowBandQuotientMGFEndpoint

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R223LowBandSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift
open ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Parameterized low-band raw envelope obtained from a quotient spike budget. -/
def lowBandParamScaledBound (G : Finset F) (τ Cbulk Kquot : ℝ) (θ : ℝ) : ℝ :=
  lowBandBulkSpikesBound (F := F) τ Cbulk (Kquot * (G.card : ℝ)) θ

/-- Above a low-band cutoff, a parameterized quotient tail lifts to the raw
nonzero-frequency tail with the same bulk constant and spike budget scaled by
`|G|`. -/
theorem nonzeroNormalizedSqAboveLowBandTail_param_scaled_of_quotient
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (τ Cbulk Kquot : ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, τ < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, τ < θ →
      (G.card : ℝ) * Bq θ ≤
        Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)) :
    ∀ θ ∈ Θ, τ < θ →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ) := by
  intro θ hθ habove
  calc
    (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ
    _ ≤ (G.card : ℝ) * Bq θ := by
      exact mul_le_mul_of_nonneg_left (hQTailAbove θ hθ habove) (by positivity)
    _ ≤ Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ) :=
      hScaleAbove θ hθ habove

/-- Parameterized quotient low-band tail certificate feeds the normalized-square
quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_quotient_param_lowBand_tail
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (τ Cbulk Kquot : ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTailAbove : ∀ θ ∈ Θ, τ < θ →
      (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ Bq θ))
    (hScaleAbove : ∀ θ ∈ Θ, τ < θ →
      (G.card : ℝ) * Bq θ ≤
        Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * lowBandParamScaledBound (F := F) G τ Cbulk Kquot θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_lowBand_bulkPlusSpikes_tail
    ψ G Θ δ τ Cbulk (Kquot * (G.card : ℝ)) hδ hstair
    (nonzeroNormalizedSqAboveLowBandTail_param_scaled_of_quotient
      ψ G Q qSq Θ Bq τ Cbulk Kquot hLift hQTailAbove hScaleAbove)
    hweighted

/-- Natural quotient-envelope low-band endpoint for Gauss periods. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_gauss_natural_param_lowBand_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (τ Cbulk Kquot : ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTailAbove : ∀ θ ∈ Θ, τ < θ →
      ((((nonzeroOrbitCarrier (F := F) G).filter
          (fun O => θ ≤ qSq O)).card : ℝ) ≤
        ParamQuotientEnvelope (F := F) G Cbulk Kquot θ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * lowBandParamScaledBound (F := F) G τ Cbulk Kquot θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  refine nonzeroNormalizedSqQuarterMGFResidual_of_quotient_param_lowBand_tail
    ψ G (nonzeroOrbitCarrier (F := F) G) qSq Θ δ
    (ParamQuotientEnvelope (F := F) G Cbulk Kquot) τ Cbulk Kquot ?_ hQTailAbove ?_
    hδ hstair hweighted
  · exact rawNonzeroTailLeCosetScale_of_gauss_orbit_score ψ G hG Θ qSq hqSq
  · intro θ _hθ _habove
    exact paramQuotientEnvelope_scale_le_raw G hG Cbulk Kquot θ

end

end ArkLib.ProximityGap.Frontier.R230ParamLowBandQuotientMGFEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R230ParamLowBandQuotientMGFEndpoint.nonzeroNormalizedSqAboveLowBandTail_param_scaled_of_quotient
#print axioms
  ArkLib.ProximityGap.Frontier.R230ParamLowBandQuotientMGFEndpoint.nonzeroNormalizedSqQuarterMGFResidual_of_quotient_param_lowBand_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R230ParamLowBandQuotientMGFEndpoint.nonzeroNormalizedSqQuarterMGFResidual_of_gauss_natural_param_lowBand_tail
