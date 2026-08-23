/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRExponentialSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# The quadratic Gauss-sum norm `‖τ‖² = p` (#389)

For the quadratic character `χ = chiC` to `ℂ` and a primitive additive character `ψ`, the Gauss
sum `τ = gaussSum χ ψ` has squared norm equal to `p`:

> **`gaussSum_normSq`** — for `p ≠ 2`, `‖gaussSum chiC ψ‖² = p`.

Proof avoids conjugation: `‖τ‖² = ‖τ²‖` (`norm_pow`) and `τ² = χ(−1)·p` (`gaussSum_sq`), so
`‖τ‖² = ‖χ(−1)‖·‖p‖ = 1·p = p` (since `χ(−1) = ±1`). This is the remaining analytic input — together
with `τ² = χ(−1)p` (the mod-4 split) and `∑χ = 0` — for evaluating the QR additive energy
(`QRAdditiveEnergyGaussSum`) to its closed form. Axiom-clean. Issue #389.
-/

open Finset AddChar MulChar
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- The norm of `chiC` at `-1` is `1` (it is `±1`). -/
theorem norm_chiC_neg_one : ‖chiC (p := p) (-1)‖ = 1 := by
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rcases quadraticChar_dichotomy hne with h | h <;> rw [chiC_apply, h] <;> norm_num

/-- **Quadratic Gauss-sum norm.** `‖gaussSum chiC ψ‖² = p` for `p ≠ 2`. -/
theorem gaussSum_normSq {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    ‖gaussSum chiC ψ‖ ^ 2 = (p : ℝ) := by
  have h2lt : 2 < p := (Fact.out (p := p.Prime)).two_le.lt_of_ne (Ne.symm hp2)
  have hsq : gaussSum (chiC (p := p)) ψ ^ 2 = chiC (-1) * (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_sq (chiC_ne_one h2lt) chiC_isQuadratic hψ
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have key : ‖gaussSum chiC ψ‖ ^ 2 = ‖gaussSum chiC ψ ^ 2‖ := by
    rw [pow_two, ← norm_mul, ← pow_two]
  rw [key, hsq, norm_mul, norm_chiC_neg_one, one_mul, Complex.norm_natCast, hcard]

end ArkLib.ProximityGap.QRExpSum

#print axioms ArkLib.ProximityGap.QRExpSum.gaussSum_normSq
