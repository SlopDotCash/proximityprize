/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R224 quotient-tail auto-carrier prize)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R221NonzeroCarrierPrizeEndpoint
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R223QuotientTailToScaledSpikePrize

/-!
# R224 (#466): quotient-tail certificates with automatic carrier positivity

R223 (`QuotientTailToScaledSpikePrize`) packages the route from an abstract
quotient-tail certificate to the corrected raw `(3/5, 2 * |G|)` scaled-spike
prize endpoint.  That theorem still exposed the R168 carrier-positivity
hypothesis.

R221 proves that this carrier positivity is automatic for `nonzeroFreqs`.  This
file composes the two facts, leaving only the genuine analytic inputs:

* the quotient survival certificate,
* the raw-to-quotient counting lift,
* the scalar envelope comparison,
* the finite staircase/weighted budget,
* and the downstream moment bridge.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R224QuotientTailAutoCarrierPrize

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- A quotient-tail certificate feeds the corrected scaled-spike prize endpoint,
with nonzero-carrier positivity supplied automatically. -/
theorem prize_sq_of_quotient_threeFifths_plus_two_tail_autoCarrier
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
    (hr : 1 ≤ r) (hrQ : Real.log Qfield ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Qfield * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_quotient_threeFifths_plus_two_tail
    ψ G hζ hdisj hσ Q qSq Θ δ Bq hLift hQTail hScale hδ hstair hweighted
    depth hcard hMmax hn hQfield nonzeroFreqs_card_pos_real hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R224QuotientTailAutoCarrierPrize

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R224QuotientTailAutoCarrierPrize.prize_sq_of_quotient_threeFifths_plus_two_tail_autoCarrier
