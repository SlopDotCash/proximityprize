/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R218 nonzero survival-to-prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R217NonzeroDilationOneChildSqMGFEndpoint

/-!
# R218 (#466): nonzero normalized-square survival certificate to prize

R216 specializes the finite survival/count layer-cake bridge to the exact R213
one-child analytic residual.  R217 then wires that residual into the concrete
nonprincipal Gauss-period dilation endpoint.

This file composes them.  A finite threshold-grid survival certificate for

```text
b ↦ ‖η_G(b)‖² / σ²,  b ≠ 0
```

now directly implies the R168/S11 squared prize bound for the normalized
dilation parent, assuming the standard moment bridge.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R218NonzeroSurvivalToPrizeEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- A nonzero normalized-square survival-grid certificate for one child of the
Gauss-period dilation recursion implies the concrete R168/S11 squared prize
bound. -/
theorem prize_sq_of_nonzero_normalizedSq_survival_count_ceiling
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (Θ : Finset ℝ) (δ B : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ B)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * B θ)
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
    nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
      ψ G Θ δ B hδ hstair hTail hweighted
  exact prize_sq_of_nonzero_dilation_one_child_sqMGFResidual
    ψ G hζ hdisj depth hσ hcard hMGF hMmax hn hQ hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R218NonzeroSurvivalToPrizeEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R218NonzeroSurvivalToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_survival_count_ceiling
