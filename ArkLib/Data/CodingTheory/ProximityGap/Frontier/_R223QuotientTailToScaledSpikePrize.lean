/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R223 quotient tail to scaled-spike prize)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R222NonzeroScaledSpikeToPrizeEndpoint

/-!
# R223 (#466): quotient tail certificates feed the scaled-spike endpoint

R220 showed that quotient-coset spike budgets should not be read literally on
the raw nonzero-frequency carrier.  R222 records the corrected raw endpoint with
spike budget `2 * |G|`.  This file packages the exact consumer needed to use a
quotient-tail certificate: a quotient count, a raw-to-quotient counting lift, and
the scalar inequality that turns the quotient envelope into the R222 raw
envelope.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- A grid tail bound on an abstract quotient carrier.  The value `qSq i`
should be the normalized square attached to quotient representative `i`. -/
def QuotientNormalizedSqGridTail {ι : Type*} (Q : Finset ι) (qSq : ι → ℝ)
    (Θ : Finset ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Θ, (((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) ≤ B θ)

/-- The raw nonzero tail count is controlled by at most `|G|` raw frequencies
per quotient survivor.  This is the formal shape of the quotient-to-raw lift
isolated by R220. -/
def RawNonzeroTailLeCosetScale {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (σ : ℝ) (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ)
      ≤ (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ))

/-- Quotient tail plus a raw-to-quotient counting lift gives the corrected raw
`(3/5, 2 * |G|)` tail envelope consumed by R222. -/
theorem nonzeroNormalizedSqGridTail_threeFifths_scaledTwo_of_quotient
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (Bq : ℝ → ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTail : QuotientNormalizedSqGridTail Q qSq Θ Bq)
    (hScale : ∀ θ ∈ Θ,
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)) :
    NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)) := by
  intro θ hθ
  calc
    (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
        (G.card : ℝ) * ((Q.filter (fun i => θ ≤ qSq i)).card : ℝ) :=
      hLift θ hθ
    _ ≤ (G.card : ℝ) * Bq θ := by
      exact mul_le_mul_of_nonneg_left (hQTail θ hθ) (by positivity)
    _ ≤ (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ) :=
      hScale θ hθ

/-- Prize endpoint driven by a quotient-tail certificate.  The theorem keeps
the genuinely analytic quotient-to-raw lift explicit and then feeds the corrected
scaled-spike raw endpoint from R222. -/
theorem prize_sq_of_quotient_threeFifths_plus_two_tail
    {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Q : Finset ι) (qSq : ι → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (hLift : RawNonzeroTailLeCosetScale ψ G σ Q qSq Θ)
    (hQTail : QuotientNormalizedSqGridTail Q qSq Θ Bq)
    (hScale : ∀ θ ∈ Θ,
      (G.card : ℝ) * Bq θ ≤
        (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)))
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
        (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)) :=
    nonzeroNormalizedSqGridTail_threeFifths_scaledTwo_of_quotient
      ψ G Q qSq Θ Bq hLift hQTail hScale
  exact prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail
    ψ G hζ hdisj hσ Θ δ hδ hstair hTail hweighted
    depth hcard hMmax hn hQfield hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize.nonzeroNormalizedSqGridTail_threeFifths_scaledTwo_of_quotient
#print axioms
  ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize.prize_sq_of_quotient_threeFifths_plus_two_tail
