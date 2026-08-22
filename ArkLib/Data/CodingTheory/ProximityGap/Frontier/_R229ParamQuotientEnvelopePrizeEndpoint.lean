/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R229 parameterized quotient envelope endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R225GaussOrbitTailLift
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R219NonzeroBulkSpikesToPrizeEndpoint

/-!
# R229 (#466): parameterized quotient envelopes to prize

R228 refuted the universal natural quotient envelope with constants `(3/5, 2)`.
The quotient-to-raw and prize bookkeeping should not be tied to those constants.
This file exposes the same endpoint for arbitrary quotient constants
`Cbulk, Kquot`, lifting them to the raw nonzero-frequency carrier as

```text
Cbulk * #(b != 0) * exp(-θ/2) + Kquot * |G|.
```

The remaining analytic task can now search for the best true quotient law
without changing the prize bridge.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The quotient-orbit half-rate bulk-plus-spikes envelope with arbitrary
constants. -/
def ParamQuotientEnvelope (G : Finset F) (Cbulk Kquot : ℝ) : ℝ → ℝ :=
  fun θ => Cbulk * (((nonzeroFreqs (F := F)).card : ℝ) / (G.card : ℝ)) *
      Real.exp (-(θ / 2)) + Kquot

/-- The all-threshold parameterized quotient-orbit tail law. -/
def ParamQuotientTailLaw (G : Finset F) (qSq : Finset F → ℝ)
    (Cbulk Kquot : ℝ) : Prop :=
  ∀ θ : ℝ,
    (((nonzeroOrbitCarrier (F := F) G).filter (fun Q => θ ≤ qSq Q)).card : ℝ) ≤
      ParamQuotientEnvelope (F := F) G Cbulk Kquot θ

/-- An all-threshold parameterized quotient tail law supplies the finite
grid-tail certificate consumed by the parameterized endpoint. -/
theorem quotientGridTail_of_paramTailLaw
    (G : Finset F) (qSq : Finset F → ℝ) (Θ : Finset ℝ)
    (Cbulk Kquot : ℝ)
    (hTail : ParamQuotientTailLaw (F := F) G qSq Cbulk Kquot) :
    QuotientNormalizedSqGridTail (nonzeroOrbitCarrier (F := F) G) qSq Θ
      (ParamQuotientEnvelope (F := F) G Cbulk Kquot) := by
  intro θ _hθ
  exact hTail θ

/-- The parameterized quotient envelope scales to the corresponding raw
nonzero-frequency envelope. -/
theorem paramQuotientEnvelope_scale_le_raw
    (G : Finset F)
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (Cbulk Kquot θ : ℝ) :
    (G.card : ℝ) * ParamQuotientEnvelope (F := F) G Cbulk Kquot θ ≤
      Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ) := by
  have hGposNat : 0 < G.card :=
    Finset.card_pos.mpr ⟨1, hG.one_mem⟩
  have hGne : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast hGposNat.ne'
  unfold ParamQuotientEnvelope
  apply le_of_eq
  field_simp [hGne]

/-- Quotient tail plus raw-to-quotient lift gives a raw nonzero-frequency tail
with the same bulk constant and spike budget multiplied by `|G|`. -/
theorem nonzeroNormalizedSqGridTail_param_scaled_of_quotient
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (Cbulk Kquot : ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTail : QuotientNormalizedSqGridTail Q qSq Θ Bq)
    (hScale : ∀ θ ∈ Θ,
      (G.card : ℝ) * Bq θ ≤
        Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)) :
    NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)) := by
  intro θ hθ
  calc
    (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ
    _ ≤ (G.card : ℝ) * Bq θ := by
      exact mul_le_mul_of_nonneg_left (hQTail θ hθ) (by positivity)
    _ ≤ Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ) :=
      hScale θ hθ

/-- Parameterized quotient-tail prize endpoint. -/
theorem prize_sq_of_quotient_param_tail
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (Cbulk Kquot : ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTail : QuotientNormalizedSqGridTail Q qSq Θ Bq)
    (hScale : ∀ θ ∈ Θ,
      (G.card : ℝ) * Bq θ ≤
        Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (depth : ℕ) {Mmax n Qfield : ℝ} {r : ℕ}
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQfield : 0 < Qfield)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Qfield ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Qfield * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  have hTail :
      NonzeroNormalizedSqGridTail ψ G σ Θ
        (fun θ => Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)) :=
    nonzeroNormalizedSqGridTail_param_scaled_of_quotient
      ψ G Q qSq Θ Bq Cbulk Kquot hLift hQTail hScale
  exact prize_sq_of_nonzero_normalizedSq_halfRate_bulkPlusSpikes_tail
    ψ G hζ hdisj hσ Θ δ Cbulk (Kquot * (G.card : ℝ))
    hδ hstair hTail hweighted depth hcard hMmax hn hQfield hP hr hrQ hmoment

/-- Natural parameterized quotient-orbit endpoint, using `ParamQuotientEnvelope`
as the quotient tail bound. -/
theorem prize_sq_of_natural_quotient_param_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kquot : ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTail :
      QuotientNormalizedSqGridTail (nonzeroOrbitCarrier (F := F) G) qSq Θ
        (ParamQuotientEnvelope (F := F) G Cbulk Kquot))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (depth : ℕ) {Mmax n Qfield : ℝ} {r : ℕ}
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQfield : 0 < Qfield)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Qfield ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Qfield * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_quotient_param_tail
    ψ G hζ hdisj hσ (nonzeroOrbitCarrier (F := F) G) qSq Θ δ
    (ParamQuotientEnvelope (F := F) G Cbulk Kquot) Cbulk Kquot ?_ hQTail ?_
    hδ hstair hweighted depth hcard hMmax hn hQfield hP hr hrQ hmoment
  · exact rawNonzeroTailLeCosetScale_of_gauss_orbit_score ψ G hG Θ qSq hqSq
  · intro θ _hθ
    exact paramQuotientEnvelope_scale_le_raw G hG Cbulk Kquot θ

/-- Natural parameterized endpoint from an all-threshold quotient-orbit tail
law.  This is the probe-facing form for arbitrary constants. -/
theorem prize_sq_of_natural_quotient_param_tailLaw
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kquot : ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTail : ParamQuotientTailLaw (F := F) G qSq Cbulk Kquot)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kquot * (G.card : ℝ)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (depth : ℕ) {Mmax n Qfield : ℝ} {r : ℕ}
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQfield : 0 < Qfield)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Qfield ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Qfield * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_natural_quotient_param_tail
    ψ G hG hζ hdisj hσ qSq Θ δ Cbulk Kquot hqSq
    (quotientGridTail_of_paramTailLaw G qSq Θ Cbulk Kquot hQTail)
    hδ hstair hweighted depth hcard hMmax hn hQfield hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.quotientGridTail_of_paramTailLaw
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.paramQuotientEnvelope_scale_le_raw
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.nonzeroNormalizedSqGridTail_param_scaled_of_quotient
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.prize_sq_of_quotient_param_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.prize_sq_of_natural_quotient_param_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R229ParamQuotientEnvelopePrizeEndpoint.prize_sq_of_natural_quotient_param_tailLaw
