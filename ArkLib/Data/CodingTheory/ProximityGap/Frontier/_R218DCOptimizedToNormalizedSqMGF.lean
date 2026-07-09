/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R218 DC-optimized bound to normalized-square MGF)
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R217NonzeroNormalizedSqCutoffMGF

/-!
# R218 (#466): DC-optimized sup bound discharges the normalized-square MGF

R217 shows that the R213 one-child residual follows from the concrete cutoff

```text
‖η_G(b)‖² / σ² ≤ 4 * log 2
```

over nonzero frequencies.  The existing `DCOptimized` theorem gives, from the
DC-subtracted energy residual at order `r ≥ log |F|`,

```text
‖η_G(b)‖² ≤ 2 * e * |G| * r
```

for every nonzero `b`.  This file welds the two statements: if the normalization
scale satisfies

```text
(2 * e * |G| * r) / σ² ≤ 4 * log 2,
```

then the R213 nonzero normalized-square quarter-MGF residual follows.

The open mathematical content remains the DC-subtracted energy estimate and
the choice of a normalization scale strong enough for the displayed inequality.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R218DCOptimizedToNormalizedSqMGF

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.DCOptimized
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R217NonzeroNormalizedSqCutoffMGF
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- DC-optimized pointwise control plus the exact R217 normalization scale gives
the R213 nonzero normalized-square quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_dcOptimized_scale
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} {σ : ℝ}
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r)
    (hDC : DCEnergyBound G r)
    (hscale :
      (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) / σ ^ 2
        ≤ 4 * Real.log 2) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  refine nonzeroNormalizedSqQuarterMGFResidual_of_cutoff_four_log_two ψ G ?_
  intro b hb
  have hbne : b ≠ 0 := (mem_nonzeroFreqs b).mp hb
  have hsq :
      ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
    eta_sq_le_dcOptimized hψ hr hrq hDC hbne
  calc
    ‖eta ψ G b‖ ^ 2 / σ ^ 2
        ≤ (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) / σ ^ 2 := by
          exact div_le_div_of_nonneg_right hsq (sq_nonneg σ)
    _ ≤ 4 * Real.log 2 := hscale

end ArkLib.ProximityGap.Frontier.R218DCOptimizedToNormalizedSqMGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R218DCOptimizedToNormalizedSqMGF.nonzeroNormalizedSqQuarterMGFResidual_of_dcOptimized_scale
