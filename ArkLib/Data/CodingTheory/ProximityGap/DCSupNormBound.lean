/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCMomentSupBound

/-!
# The DC-subtracted per-frequency sup-norm bound (#407)

Taking the `r`-th root of the DC-subtracted power bound (`eta_pow_le_dc`) gives the sharp per-order
bound on the squared Gauss period at every non-trivial frequency:

> **`eta_sq_le_dc`** — for `b ≠ 0`, `‖η_b‖² ≤ (q·E_r(G) − |G|^{2r})^{1/r}`.

Minimizing the right side over `r` (optimum `r ≈ ln q`) yields `M(n) = max_{b≠0}‖η_b‖ ≤ √(2n ln q)`
(the prize sup-norm), conditional on the energy bound `E_r ≤ (2r−1)‼·|G|^r`. This is the DC-subtracted
companion of `GaussPeriodOptimizedBound`, isolating exactly the `b ≠ 0` content `M` controls.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCMomentSupBound

namespace ArkLib.ProximityGap.DCSupNormBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **DC-subtracted per-frequency sup-norm bound.** For `b ≠ 0` and `r ≥ 1`,
`‖η_b‖² ≤ (q·E_r(G) − |G|^{2r})^{1/r}` — the `r`-th root of the DC-subtracted power bound. -/
theorem eta_sq_le_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} (hr : 1 ≤ r)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2
      ≤ ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) ^ ((r : ℝ)⁻¹) := by
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
    rw [← pow_mul]; exact eta_pow_le_dc hψ G r hb
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)

end ArkLib.ProximityGap.DCSupNormBound

#print axioms ArkLib.ProximityGap.DCSupNormBound.eta_sq_le_dc
