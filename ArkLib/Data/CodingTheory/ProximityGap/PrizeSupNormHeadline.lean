/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized

/-!
# The headline prize sup-norm bound at the optimal order (#407)

Instantiating the corrected `eta_sq_le_dcOptimized` at the optimal moment order `r = ⌈ln q⌉` gives the
clean, citable prize bound:

> **`prize_supNorm_bound`** — for `1 < q`, under `DCEnergyBound G ⌈ln q⌉`, every non-trivial Gauss
> period satisfies `‖η_b‖² ≤ 2e·|G|·⌈ln q⌉`, i.e. `M ≤ √(2e·n·⌈ln q⌉) = O(√(n·ln q))`.

This is the square-root-cancellation sup-norm in the prize regime, conditional only on the DC-subtracted
energy bound `DCEnergyBound G ⌈ln q⌉` (= `A_{⌈ln q⌉} ≤ Wick`, true at every prize prime; the open input
is exactly this BGK / Anomaly-Suppression inequality). Non-vacuous, unlike the in-tree non-DC route.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCOptimized

namespace ArkLib.ProximityGap.PrizeSupNormHeadline

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Headline prize sup-norm bound.** At the optimal order `r = ⌈ln q⌉`, under the corrected DC energy
bound, `‖η_b‖² ≤ 2e·|G|·⌈ln q⌉` for every `b ≠ 0` — the `√(n·ln q)`-cancellation prize bound. -/
theorem prize_supNorm_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hqc : 1 < Fintype.card F)
    (h : DCEnergyBound G ⌈Real.log (Fintype.card F)⌉₊) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * (G.card : ℝ) * (⌈Real.log (Fintype.card F)⌉₊ : ℝ) := by
  have hlogpos : 0 < Real.log (Fintype.card F) := Real.log_pos (by exact_mod_cast hqc)
  have hr : 1 ≤ ⌈Real.log (Fintype.card F)⌉₊ := Nat.one_le_ceil_iff.mpr hlogpos
  exact eta_sq_le_dcOptimized hψ hr (Nat.le_ceil _) h hb

end ArkLib.ProximityGap.PrizeSupNormHeadline
#print axioms ArkLib.ProximityGap.PrizeSupNormHeadline.prize_supNorm_bound
