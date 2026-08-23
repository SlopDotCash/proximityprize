/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R228 natural quotient tail-law endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R227NaturalQuotientEnvelopePrizeEndpoint

/-!
# R228 (#466): all-threshold natural quotient tail law to prize

R227 consumes a finite grid-tail certificate for the natural quotient envelope.
This file names the all-threshold tail law tested by the R228 probe and proves
that it immediately supplies the grid-tail input required by R227.

The remaining analytic content is exactly `NaturalQuotientTailLaw`: for every
threshold `θ`, the number of quotient orbits with normalized square at least
`θ` is bounded by

```text
(3/5) * (#(b ≠ 0) / |G|) * exp(-θ/2) + 2.
```
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R228NaturalQuotientTailLawEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.Frontier.R227NaturalQuotientEnvelopePrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The all-threshold natural quotient-orbit tail law.  This is the analytic
input probed numerically in R228; the rest of the file is bookkeeping from this
law to the already-composed prize endpoint. -/
def NaturalQuotientTailLaw (G : Finset F) (qSq : Finset F → ℝ) : Prop :=
  ∀ θ : ℝ,
    (((nonzeroOrbitCarrier (F := F) G).filter (fun Q => θ ≤ qSq Q)).card : ℝ) ≤
      NaturalQuotientEnvelope (F := F) G θ

/-- An all-threshold natural quotient tail law supplies the finite grid-tail
certificate consumed by R227. -/
theorem quotientGridTail_of_naturalTailLaw
    (G : Finset F) (qSq : Finset F → ℝ) (Θ : Finset ℝ)
    (hTail : NaturalQuotientTailLaw (F := F) G qSq) :
    QuotientNormalizedSqGridTail (nonzeroOrbitCarrier (F := F) G) qSq Θ
      (NaturalQuotientEnvelope (F := F) G) := by
  intro θ _hθ
  exact hTail θ

/-- Prize endpoint with the all-threshold natural quotient tail law.  The only
unproven analytic input is now the tail law itself. -/
theorem prize_sq_of_gauss_natural_quotient_tailLaw
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTail : NaturalQuotientTailLaw (F := F) G qSq)
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
  exact prize_sq_of_gauss_natural_quotient_tail
    ψ G hG hζ hdisj hσ qSq Θ δ hqSq
    (quotientGridTail_of_naturalTailLaw G qSq Θ hQTail)
    hδ hstair hweighted depth hcard hMmax hn hQfield hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R228NaturalQuotientTailLawEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R228NaturalQuotientTailLawEndpoint.quotientGridTail_of_naturalTailLaw
#print axioms
  ArkLib.ProximityGap.Frontier.R228NaturalQuotientTailLawEndpoint.prize_sq_of_gauss_natural_quotient_tailLaw
