/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R219 nonzero bulk-spikes to prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R217NonzeroDilationOneChildSqMGFEndpoint

/-!
# R219 (#466): nonzero bulk-plus-spikes survival tail to prize

R218 exposes the most general survival-grid certificate.  This file specializes
the concrete prize endpoint to the half-rate bulk-plus-spikes envelope used by
the current probes:

```text
#{b ≠ 0 : θ ≤ ‖η_G(b)‖² / σ²}
  ≤ Cbulk * #(b ≠ 0) * exp(-θ/2) + Kspike.
```

Together with the corresponding weighted grid budget, this lands the R213
one-child MGF residual and hence the corrected R217 nonprincipal prize-square
endpoint.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- A half-rate bulk-plus-spikes survival envelope for the nonzero normalized
square child spectrum implies the concrete nonprincipal R168/S11 squared prize
bound. -/
theorem prize_sq_of_nonzero_normalizedSq_halfRate_bulkPlusSpikes_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + Kspike))
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kspike))
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
  have hMGF :=
    nonzeroNormalizedSqQuarterMGFResidual_of_halfRate_bulkPlusSpikes_tail
      ψ G Θ δ Cbulk Kspike hδ hstair hTail hweighted
  exact prize_sq_of_nonzero_dilation_one_child_sqMGFResidual
    ψ G hζ hdisj depth hσ hcard hMGF hMmax hn hQ hP hr hrQ hmoment

/-- Literal `(3/5, 2)` specialization of the half-rate bulk-plus-spikes
survival endpoint. -/
theorem prize_sq_of_nonzero_normalizedSq_threeFifths_plus_two_tail
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + 2))
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2))
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
    ψ G hζ hdisj hσ Θ δ (3 / 5) 2 hδ hstair hTail hweighted
    depth hcard hMmax hn hQ hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_halfRate_bulkPlusSpikes_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R219NonzeroBulkSpikesToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_threeFifths_plus_two_tail
