/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R217 nonzero normalized-square cutoff MGF)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R213NonzeroNormalizedSqQuarterMGFResidualConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf

/-!
# R217 (#466): cutoff route to the nonzero normalized-square quarter-MGF residual

R213 names the exact one-child analytic socket:

```text
MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖² / σ²) 2 (1/4).
```

This file records the sharp elementary cutoff that implies it.  If every
nonzero normalized square satisfies

```text
‖η_G(b)‖² / σ² ≤ 4 * log 2,
```

then each exponential weight is at most `2`, hence the R213 residual follows.

This is not the prize proof: the cutoff is essentially a sup-norm target.  Its
purpose is to pin the exact numerical threshold for any route that proves a
uniform child-spectrum maximum.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R217NonzeroNormalizedSqCutoffMGF

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A normalized-square cutoff at `4 log 2` gives the exact nonzero
normalized-square quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_cutoff_four_log_two
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hcut : ∀ b ∈ nonzeroFreqs (F := F),
      ‖eta ψ G b‖ ^ 2 / σ ^ 2 ≤ 4 * Real.log 2) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  have hMGF : MGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2)
      (Real.exp ((1 / 4 : ℝ) * (4 * Real.log 2))) (1 / 4 : ℝ) :=
    mgfBound_of_max_ceiling (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2)
      (by positivity : 0 ≤ (1 / 4 : ℝ)) hcut
  unfold NonzeroNormalizedSqQuarterMGFResidual
  unfold MGFBound at hMGF ⊢
  simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hMGF

end ArkLib.ProximityGap.Frontier.R217NonzeroNormalizedSqCutoffMGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R217NonzeroNormalizedSqCutoffMGF.nonzeroNormalizedSqQuarterMGFResidual_of_cutoff_four_log_two
