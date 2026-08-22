/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R219 DC-optimized scale prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R218DCOptimizedToNormalizedSqMGF

/-!
# R219 (#466): DC-optimized scale certificate to the normalized-square prize endpoint

R218 discharges the R213 one-child normalized-square quarter-MGF residual from:

* `DCEnergyBound G k` at an energy order `k ≥ log |F|`;
* the normalization inequality
  `(2 * exp 1 * |G| * k) / σ² ≤ 4 * log 2`.

R213 then feeds that residual into the concrete nonzero-frequency dyadic
dilation endpoint.  This file composes those two steps and keeps the two
orders separate:

* `k` is the DC-energy order used to prove the child MGF residual;
* `r` is the downstream moment-bridge order used by the R168/S11 prize
  consumer.

No new analytic estimate is proved here.  The open inputs remain the
DC-subtracted energy bound, the normalization scale inequality, and the
standard downstream moment bridge.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R219DCOptimizedScalePrizeEndpoint

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R218DCOptimizedToNormalizedSqMGF
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- DC-optimized child control plus the exact normalization-scale inequality
imply the concrete normalized-square squared-prize endpoint. -/
theorem prize_sq_of_dcOptimized_scale
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {ζ : F} {σ : ℝ}
    {k : ℕ}
    (hk : 1 ≤ k) (hkq : Real.log (Fintype.card F) ≤ k)
    (hDC : DCEnergyBound G k)
    (hscale :
      (2 * Real.exp 1 * (G.card : ℝ) * (k : ℝ)) / σ ^ 2
        ≤ 4 * Real.log 2)
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
  have hMGF :=
    nonzeroNormalizedSqQuarterMGFResidual_of_dcOptimized_scale
      hψ G hk hkq hDC hscale
  exact prize_sq_of_nonzero_normalizedSq_quarterMGFResidual
    ψ G hζ hdisj hσ hMGF hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R219DCOptimizedScalePrizeEndpoint

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R219DCOptimizedScalePrizeEndpoint.prize_sq_of_dcOptimized_scale
