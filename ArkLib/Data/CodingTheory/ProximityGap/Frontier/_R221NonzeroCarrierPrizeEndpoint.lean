/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R221 nonzero-carrier prize endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R220DCOptimizedVarianceScalePrizeEndpoint

/-!
# R221 (#466): remove the explicit nonzero-carrier positivity hypothesis

The R168/S11 prize consumers require a positive carrier cardinality.  On the
nonprincipal spectrum this is automatic: every field has `1 ≠ 0`, so
`1 ∈ nonzeroFreqs = univ.erase 0`.

This file packages that fact and composes it with R220, removing the explicit

```text
hP : 0 < ((nonzeroFreqs).card : ℝ)
```

assumption from the DC-optimized variance-scale endpoint.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R220DCOptimizedVarianceScalePrizeEndpoint
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero-frequency carrier is nonempty: it contains `1`. -/
theorem one_mem_nonzeroFreqs : (1 : F) ∈ nonzeroFreqs (F := F) := by
  rw [mem_nonzeroFreqs]
  exact one_ne_zero

/-- The nonzero-frequency carrier has positive real cardinality. -/
theorem nonzeroFreqs_card_pos_real :
    0 < ((nonzeroFreqs (F := F)).card : ℝ) := by
  have hnat : 0 < (nonzeroFreqs (F := F)).card :=
    Finset.card_pos.mpr ⟨1, one_mem_nonzeroFreqs (F := F)⟩
  exact_mod_cast hnat

/-- R220's DC-optimized variance-scale prize endpoint with the nonzero-carrier
positivity hypothesis discharged automatically. -/
theorem prize_sq_of_dcOptimized_variance_scale_autoCarrier
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
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dcOptimized_variance_scale
    hψ G hk hkq hDC hvariance hζ hdisj hσ
    hMmax hn hQ nonzeroFreqs_card_pos_real hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint.one_mem_nonzeroFreqs
#print axioms ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint.nonzeroFreqs_card_pos_real
#print axioms ArkLib.ProximityGap.Frontier.R221NonzeroCarrierPrizeEndpoint.prize_sq_of_dcOptimized_variance_scale_autoCarrier
