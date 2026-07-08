/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R213 nonzero normalized-square quarter-MGF residual consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R211NonzeroNormalizedSqDilationConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

/-!
# R213 (#466): name the nonzero normalized-square quarter-MGF residual

R211 sharpened the nonprincipal dilation bridge to the normalized-square
spectrum

```text
X_G(b) = ‖η_G(b)‖² / σ².
```

This file gives the remaining one-child analytic input the same clean
`MGFBound` interface used throughout the R168/R188/R209 tower route:

```text
MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖² / σ²) 2 (1/4).
```

No concentration estimate is proved here.  The theorem below only composes
that named residual with the concrete R211 nonzero normalized-square dilation
consumer.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The named nonzero quarter-MGF residual for the normalized-square
Gauss-period spectrum. -/
def NonzeroNormalizedSqQuarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ) : Prop :=
  MGFBound (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2) 2 (1 / 4 : ℝ)

/-- Unfold the named normalized-square residual into the raw R211 sum budget. -/
theorem raw_quarter_sum_of_nonzeroNormalizedSqQuarterMGFResidual
    {ψ : AddChar F ℂ} {G : Finset F} {σ : ℝ}
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)))
      ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ) := by
  exact hMGF

/-- `MGFBound` form of R211's nonzero-frequency normalized-square dyadic-tail
consumer. -/
theorem dyadicTailMGF_of_nonzero_normalizedSq_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ) :
    DyadicTailMGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) := by
  exact dyadicTailMGF_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
    ψ G hζ hdisj hσ
    (raw_quarter_sum_of_nonzeroNormalizedSqQuarterMGFResidual hMGF)

/-- Prize-square endpoint with the remaining analytic input named as a
nonzero normalized-square quarter-MGF residual. -/
theorem prize_sq_of_nonzero_normalizedSq_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
    ψ G hζ hdisj hσ
    (raw_quarter_sum_of_nonzeroNormalizedSqQuarterMGFResidual hMGF)
    hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer.raw_quarter_sum_of_nonzeroNormalizedSqQuarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer.dyadicTailMGF_of_nonzero_normalizedSq_quarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer.prize_sq_of_nonzero_normalizedSq_quarterMGFResidual
