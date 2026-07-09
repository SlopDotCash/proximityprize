/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R207 tower-step dilation prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumTowerL2
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R206GaussPeriodDilationPrizeConsumer

/-!
# R207 (#466): apply the concrete dilation consumer at any tower level

R206 removes the abstract parent from the one-step dilation recursion:

```text
G ↦ G ∪ ζ • G.
```

The tower substrate packages the repeated dyadic recursion as
`towerStep G₀ ζ (k+1) = towerStep G₀ ζ k ∪ ζ k • towerStep G₀ ζ k`.
This file exposes the direct composition: every valid tower step inherits the
R206 dyadic-tail and prize-square consumers from a one-child quarter-MGF bound
at the previous level.

The analytic input is still exactly the same one-child quarter-MGF estimate,
now indexed by the tower level `k`.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Reindexed R198-route dyadic-tail consumer at one valid tower step. -/
theorem dyadicTailMGF_of_towerStep_reindexed_quarter
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ)
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (towerStep G₀ ζ k) b‖)) :
    DyadicTailMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (towerStep G₀ ζ (k + 1)) b‖) := by
  simpa [towerStep_succ] using
    dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter ψ (towerStep G₀ ζ k)
      (hvalid.ne_zero k hk) (hvalid.disjoint k hk) hLeft

/-- Sum-bound version of the tower-step dyadic-tail consumer. -/
theorem dyadicTailMGF_of_towerStep_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ)
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ (towerStep G₀ ζ k) b‖))
        ≤ 2 * (Fintype.card F : ℝ)) :
    DyadicTailMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (towerStep G₀ ζ (k + 1)) b‖) := by
  exact dyadicTailMGF_of_towerStep_reindexed_quarter ψ G₀ ζ hvalid hk
    (by simpa [DyadicQuarterMGFBound] using hLeft)

/-- Reindexed R198-route prize-square endpoint at one valid tower step. -/
theorem prize_sq_of_towerStep_reindexed_quarter
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (towerStep G₀ ζ k) b‖))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (towerStep G₀ ζ (k + 1)) b‖) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  simpa [towerStep_succ] using
    prize_sq_of_gaussPeriod_dilation_reindexed_quarter ψ (towerStep G₀ ζ k)
      (hvalid.ne_zero k hk) (hvalid.disjoint k hk) hLeft
      hMmax hn hQ hP hr hrQ (by simpa [towerStep_succ] using hmoment)

/-- Sum-bound version of the tower-step prize-square endpoint. -/
theorem prize_sq_of_towerStep_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ (towerStep G₀ ζ k) b‖))
        ≤ 2 * (Fintype.card F : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (towerStep G₀ ζ (k + 1)) b‖) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_towerStep_reindexed_quarter ψ G₀ ζ hvalid hk
    (by simpa [DyadicQuarterMGFBound] using hLeft)
    hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer.dyadicTailMGF_of_towerStep_reindexed_quarter
#print axioms ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer.dyadicTailMGF_of_towerStep_reindexed_quarter_sum
#print axioms ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer.prize_sq_of_towerStep_reindexed_quarter
#print axioms ArkLib.ProximityGap.Frontier.R207TowerStepDilationPrizeConsumer.prize_sq_of_towerStep_reindexed_quarter_sum
