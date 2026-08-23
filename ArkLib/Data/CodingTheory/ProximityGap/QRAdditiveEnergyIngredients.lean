/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QuadraticGaussSumNorm

/-!
# Ingredients for the QR additive-energy closed form (#389)

Two facts that, with `qr_energy_gaussSum` (`p·E = |QR|⁴ + (1/16)∑_{b≠0}‖χ(b)τ−1‖⁴`), reduce the QR
additive energy to elementary arithmetic in `Re τ`:

> **`norm_sq_term`** — for `b ≠ 0`, `‖χ(b)·τ − 1‖² = p + 1 − 2·(χ b).re·(τ).re`.
> **`sum_chiC_erase_zero`** — `∑_{b≠0} χ(b) = 0`.

Squaring `norm_sq_term` and summing (using `∑χ=0`, `∑χ²=p−1`) gives
`∑_{b≠0}‖χ(b)τ−1‖⁴ = (p−1)((p+1)² + 4(Re τ)²)`, and `(Re τ)² = p` (`p≡1 mod 4`) / `0` (`p≡3 mod 4`)
from `τ² = χ(−1)p` (`gaussSum_sq`) with `‖τ‖²=p` (`gaussSum_normSq`) — yielding the closed form
`(p−1)(p²−2p+9)/16` / `(p−1)(p²−2p+5)/16`. Axiom-clean. Issue #389.
-/

open Finset AddChar MulChar Complex
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- **Per-frequency norm.** For `b ≠ 0`, `‖χ(b)·τ − 1‖² = p + 1 − 2·(χ b).re·(τ).re`. -/
theorem norm_sq_term {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) :
    ‖chiC b * gaussSum chiC ψ - 1‖ ^ 2
      = (p : ℝ) + 1 - 2 * (chiC b).re * (gaussSum chiC ψ).re := by
  have hdich : chiC (p := p) b = 1 ∨ chiC b = -1 := by
    rcases quadraticChar_dichotomy hb with h | h <;> [left; right] <;> simp [chiC_apply, h]
  have hntau : Complex.normSq (gaussSum chiC ψ) = (p : ℝ) := by
    rw [Complex.normSq_eq_norm_sq]; exact gaussSum_normSq hψ hp2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_mul, hntau]
  rcases hdich with h | h <;> rw [h] <;>
    simp [Complex.normSq_one, Complex.normSq_neg, Complex.mul_re, Complex.one_re,
      Complex.one_im, Complex.neg_re, Complex.neg_im, map_one] <;> ring

/-- **Nontrivial character sum.** `∑_{b≠0} χ(b) = 0`. -/
theorem sum_chiC_erase_zero (hp2 : p ≠ 2) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p), chiC (p := p) b = 0 := by
  have h2lt : 2 < p := (Fact.out (p := p.Prime)).two_le.lt_of_ne (Ne.symm hp2)
  rw [Finset.sum_erase Finset.univ chiC_zero]
  exact MulChar.sum_eq_zero_of_ne_one (chiC_ne_one h2lt)

end ArkLib.ProximityGap.QRExpSum

#print axioms ArkLib.ProximityGap.QRExpSum.norm_sq_term
#print axioms ArkLib.ProximityGap.QRExpSum.sum_chiC_erase_zero
