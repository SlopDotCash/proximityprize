/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R209 nonzero quarter-MGF residual consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R207NonzeroGaussPeriodDilationConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

/-!
# R209 (#466): nonzero quarter-MGF residual as an `MGFBound`

R207 isolated the remaining analytic input as the raw sum inequality

```text
Σ_{b≠0} exp((1/4) * ‖η_G(b)‖) ≤ 2 * #(b ≠ 0).
```

The concentration/layer-cake cone already names exactly this shape as
`WFS11.MGFBound s t A c`.  This file repackages the R207 endpoint so the
remaining prize obligation is the single named residual

```text
MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖) 2 (1/4).
```

No analytic estimate is proved here; this is the final interface cleanup before
attacking the MGF/survival bound itself.
-/

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The named nonzero quarter-MGF residual for a Gauss-period spectrum. -/
def NonzeroQuarterMGFResidual (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  MGFBound (nonzeroFreqs (F := F)) (fun b => ‖eta ψ G b‖) 2 (1 / 4 : ℝ)

/-- Unfold the named residual into the raw R207 sum budget. -/
theorem raw_quarter_sum_of_nonzeroQuarterMGFResidual
    {ψ : AddChar F ℂ} {G : Finset F}
    (hMGF : NonzeroQuarterMGFResidual ψ G) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
      ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ) := by
  exact hMGF

/-- `MGFBound` form of R207's nonzero-frequency dyadic-tail consumer. -/
theorem dyadicTailMGF_of_nonzero_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hMGF : NonzeroQuarterMGFResidual ψ G) :
    DyadicTailMGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  exact dyadicTailMGF_of_nonzero_gaussPeriod_dilation_quarter ψ G hζ hdisj
    (raw_quarter_sum_of_nonzeroQuarterMGFResidual hMGF)

/-- Prize-square endpoint with the remaining analytic input named as a nonzero
quarter-MGF residual. -/
theorem prize_sq_of_nonzero_quarterMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hMGF : NonzeroQuarterMGFResidual ψ G)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_nonzero_gaussPeriod_dilation_quarter ψ G hζ hdisj
    (raw_quarter_sum_of_nonzeroQuarterMGFResidual hMGF)
    hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.raw_quarter_sum_of_nonzeroQuarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.dyadicTailMGF_of_nonzero_quarterMGFResidual
#print axioms ArkLib.ProximityGap.Frontier.R209NonzeroQuarterMGFResidualConsumer.prize_sq_of_nonzero_quarterMGFResidual
