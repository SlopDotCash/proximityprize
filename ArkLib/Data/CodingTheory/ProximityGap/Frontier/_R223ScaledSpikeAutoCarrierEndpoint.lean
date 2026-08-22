/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R223 scaled-spike auto-carrier endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R221NonzeroCarrierPrizeEndpoint
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R222NonzeroScaledSpikeToPrizeEndpoint

/-!
# R223 (#466): scaled-spike endpoint without explicit carrier positivity

R222 corrected the raw nonzero-frequency spike endpoint by replacing a literal
raw `+2` allowance with the quotient-safe raw allowance `+2 * |G|`.  R221 proved
that the nonzero-frequency carrier is automatically nonempty over every field.

This file composes the two facts: the scaled-spike endpoint no longer exposes
the artificial hypothesis

```text
hP : 0 < ((nonzeroFreqs).card : ℝ)
```

to downstream consumers.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R223ScaledSpikeAutoCarrierEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint
open ArkLib.ProximityGap.Frontier.R222NonzeroScaledSpikeToPrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- R222's raw-frequency-safe `(3/5, 2 * |G|)` spike endpoint with the
nonzero-carrier positivity hypothesis discharged automatically. -/
theorem prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail_autoCarrier
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
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail
    ψ G hζ hdisj hσ Θ δ hδ hstair hTail hweighted depth hcard hMmax hn hQ
    nonzeroFreqs_card_pos_real hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R223ScaledSpikeAutoCarrierEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R223ScaledSpikeAutoCarrierEndpoint.prize_sq_of_nonzero_normalizedSq_threeFifths_plus_scaledTwo_tail_autoCarrier
