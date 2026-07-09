/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R226 Gauss quotient-tail prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R225GaussOrbitTailLift

/-!
# R226 (#466): Gauss quotient-tail certificate to prize

R223 consumes an abstract quotient-tail certificate plus a raw-to-quotient lift.
R225 proves that lift for Gauss periods from coset invariance.  This file
packages the composed endpoint: a quotient-orbit grid tail, a quotient score
dominating each raw orbit survivor, and the scaled envelope inequality imply
the R168/S11 nonprincipal prize-square bound.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R226GaussQuotientTailPrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R223QuotientTailToScaledSpikePrize
open ArkLib.ProximityGap.Frontier.R224OrbitTailLiftToQuotientTail
open ArkLib.ProximityGap.Frontier.R225GaussOrbitTailLift
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Gauss-period quotient-tail endpoint: the abstract raw-to-quotient lift in
R223 is discharged by R225's coset-invariance/orbit-stability theorem. -/
theorem prize_sq_of_gauss_quotient_threeFifths_plus_two_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hG : ArkLib.ProximityGap.E2DilationDirectCount.FinSubgroup G)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (qSq : Finset F → ℝ) (Θ : Finset ℝ) (δ Bq : ℝ → ℝ)
    (hqSq : ∀ θ ∈ Θ, ∀ b ∈ nonzeroFreqs (F := F),
      θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2 →
        θ ≤ qSq (ArkLib.ProximityGap.E2DilationDirectCount.orbit G b))
    (hQTail : QuotientNormalizedSqGridTail (nonzeroOrbitCarrier (F := F) G) qSq Θ Bq)
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
  have hLift :
      RawNonzeroTailLeCosetScale ψ G σ (nonzeroOrbitCarrier (F := F) G) qSq Θ :=
    rawNonzeroTailLeCosetScale_of_gauss_orbit_score ψ G hG Θ qSq hqSq
  exact prize_sq_of_quotient_threeFifths_plus_two_tail
    ψ G hζ hdisj hσ (nonzeroOrbitCarrier (F := F) G) qSq Θ δ Bq
    hLift hQTail hScale hδ hstair hweighted depth hcard hMmax hn
    hQfield hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R226GaussQuotientTailPrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R226GaussQuotientTailPrizeEndpoint.prize_sq_of_gauss_quotient_threeFifths_plus_two_tail
