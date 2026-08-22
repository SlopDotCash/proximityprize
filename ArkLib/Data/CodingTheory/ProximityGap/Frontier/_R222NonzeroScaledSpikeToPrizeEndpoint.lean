/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R222 nonzero scaled-spike prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R219NonzeroBulkSpikesToPrizeEndpoint

/-!
# R222 (#466): nonzero raw-frequency scaled-spike endpoint

R219 contains a literal `(3/5, 2)` half-rate bulk-plus-spikes endpoint on the
raw nonzero frequency carrier.  The R220 quotient-vs-raw probe shows that a
quotient-coset `+2` spike budget lifts to the raw frequency carrier with the
spike term multiplied by the coset size.  This file records the corresponding
raw-frequency-safe prize endpoint with spike budget `2 * |G|`.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Raw-frequency-safe specialization of the R219 half-rate bulk-plus-spikes
endpoint: a quotient `+2` spike allowance lifted to raw frequencies is recorded
as `+ 2 * |G|`. -/
theorem prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)))
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2 * (G.card : ℝ)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (depth : ℕ) {Mmax n Q : ℝ} {r : ℕ}
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_nonzero_normalizedSq_halfRate_bulkPlusSpikes_tail
    ψ G hζ hdisj hσ Θ δ (3 / 5) (2 * (G.card : ℝ))
    hδ hstair hTail hweighted depth hcard hMmax hn hQ hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail
