/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R220 DC-optimized variance-scale prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R219DCOptimizedScalePrizeEndpoint

/-!
# R220 (#466): variance-scale form of the DC-optimized prize endpoint

R219 assumes the ratio form

```text
(2 * exp 1 * |G| * k) / σ² ≤ 4 * log 2.
```

For callers, the more natural normalization condition is the equivalent
variance lower bound

```text
2 * exp 1 * |G| * k ≤ (4 * log 2) * σ².
```

This file packages that arithmetic conversion and composes it with R219.  It
does not add analytic content; it removes one real-arithmetic chore from the
future prize-level instantiation.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R220DCOptimizedVarianceScalePrizeEndpoint

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R219DCOptimizedScalePrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Convert the variance lower-bound form of the normalization scale into the
ratio form consumed by R219. -/
theorem dcOptimized_ratio_scale_of_variance_scale
    (G : Finset F) {k : ℕ} {σ : ℝ}
    (hσ : 0 < σ)
    (hvariance :
      2 * Real.exp 1 * (G.card : ℝ) * (k : ℝ)
        ≤ (4 * Real.log 2) * σ ^ 2) :
    (2 * Real.exp 1 * (G.card : ℝ) * (k : ℝ)) / σ ^ 2
      ≤ 4 * Real.log 2 := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  rw [div_le_iff₀ hσ2]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hvariance

/-- DC-optimized child control plus a variance lower bound on the
normalization scale imply the concrete normalized-square squared-prize
endpoint. -/
theorem prize_sq_of_dcOptimized_variance_scale
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F} {σ : ℝ}
    {k : ℕ}
    (hk : 1 ≤ k) (hkq : Real.log (Fintype.card F) ≤ k)
    (hDC : DCEnergyBound G k)
    (hvariance :
      2 * Real.exp 1 * (G.card : ℝ) * (k : ℝ)
        ≤ (4 * Real.log 2) * σ ^ 2)
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dcOptimized_scale
    hψ G hk hkq hDC
    (dcOptimized_ratio_scale_of_variance_scale G hσ hvariance)
    hζ hdisj hσ hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R220DCOptimizedVarianceScalePrizeEndpoint

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R220DCOptimizedVarianceScalePrizeEndpoint.dcOptimized_ratio_scale_of_variance_scale
#print axioms ArkLib.ProximityGap.Frontier.R220DCOptimizedVarianceScalePrizeEndpoint.prize_sq_of_dcOptimized_variance_scale
