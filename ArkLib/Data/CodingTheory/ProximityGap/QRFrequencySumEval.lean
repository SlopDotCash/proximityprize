/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRAdditiveEnergyIngredients

/-!
# Evaluating the QR frequency sum (#389)

> **`tau_re_sq`** — `(Re τ)² = (p + (χ(−1)).re·p)/2`  (so `= p` for `p≡1 mod 4`, `0` for `p≡3`).
> **`sum_term_eval`** — `∑_{b≠0} ‖χ(b)τ − 1‖⁴ = (p−1)·((p+1)² + 4(Re τ)²)`.

`tau_re_sq` solves the 2×2 system `Re τ² − Im τ² = (χ(−1)).re·p` (real part of `τ²=χ(−1)p`) and
`Re τ² + Im τ² = p` (`‖τ‖²=p`). `sum_term_eval` squares `norm_sq_term` and sums via `∑χ=0`,
`∑(χ b).re²=p−1`. With `qr_energy_gaussSum` these give the QR additive-energy closed form. Axiom-clean.
Issue #389.
-/

open Finset AddChar MulChar Complex
open ArkLib.ProximityGap.QRExpSum

namespace ArkLib.ProximityGap.QRExpSum

variable {p : ℕ} [Fact p.Prime]

/-- **`(Re τ)²` value.** `(Re τ)² = (p + (χ(−1)).re·p)/2`. -/
theorem tau_re_sq {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    (gaussSum chiC ψ).re ^ 2 = ((p : ℝ) + (chiC (p := p) (-1)).re * (p : ℝ)) / 2 := by
  have h2lt : 2 < p := (Fact.out (p := p.Prime)).two_le.lt_of_ne (Ne.symm hp2)
  have hsq : gaussSum (chiC (p := p)) ψ ^ 2 = chiC (p := p) (-1) * (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_sq (chiC_ne_one h2lt) chiC_isQuadratic hψ
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hre : (gaussSum chiC ψ).re ^ 2 - (gaussSum chiC ψ).im ^ 2 = (chiC (p := p) (-1)).re * (p : ℝ) := by
    have h := congrArg Complex.re hsq
    rw [hcard] at h
    simpa [pow_two, Complex.mul_re, Complex.natCast_re, Complex.natCast_im] using h
  have hnorm : (gaussSum chiC ψ).re ^ 2 + (gaussSum chiC ψ).im ^ 2 = (p : ℝ) := by
    have h := gaussSum_normSq hψ hp2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    nlinarith [h]
  linarith [hre, hnorm]

/-- **Frequency sum.** `∑_{b≠0} ‖χ(b)τ − 1‖⁴ = (p−1)·((p+1)² + 4(Re τ)²)`. -/
theorem sum_term_eval {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (hp2 : p ≠ 2) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p), ‖chiC b * gaussSum chiC ψ - 1‖ ^ 4
      = ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 2 + 4 * (gaussSum chiC ψ).re ^ 2) := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  have hcardE : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  set τre := (gaussSum (chiC (p := p)) ψ).re with hτ
  -- rewrite ‖·‖⁴ termwise via norm_sq_term
  have hterm : ∀ b ∈ Finset.univ.erase (0 : ZMod p),
      ‖chiC b * gaussSum chiC ψ - 1‖ ^ 4
        = ((p : ℝ) + 1) ^ 2 - 4 * ((p : ℝ) + 1) * τre * (chiC b).re
          + 4 * τre ^ 2 * ((chiC b).re ^ 2) := by
    intro b hb
    have hbne : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have h2 := norm_sq_term hψ hp2 hbne
    have h4 : ‖chiC b * gaussSum chiC ψ - 1‖ ^ 4
        = (‖chiC b * gaussSum chiC ψ - 1‖ ^ 2) ^ 2 := by ring
    rw [h4, h2]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- ∑ (p+1)² = (p−1)(p+1)²
  have hA : ∑ _b ∈ Finset.univ.erase (0 : ZMod p), ((p : ℝ) + 1) ^ 2
      = ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 := by
    rw [Finset.sum_const, hcardE, nsmul_eq_mul, Nat.cast_sub hp1, Nat.cast_one]
  -- ∑ (χ b).re = 0
  have hB0 : ∑ b ∈ Finset.univ.erase (0 : ZMod p), (chiC b).re = 0 := by
    rw [← Complex.re_sum, sum_chiC_erase_zero hp2, Complex.zero_re]
  have hB : ∑ b ∈ Finset.univ.erase (0 : ZMod p),
      4 * ((p : ℝ) + 1) * τre * (chiC b).re = 0 := by
    rw [← Finset.mul_sum, hB0, mul_zero]
  -- ∑ (χ b).re² = p − 1
  have hC1 : ∑ b ∈ Finset.univ.erase (0 : ZMod p), ((chiC b).re ^ 2) = ((p : ℝ) - 1) := by
    have : ∀ b ∈ Finset.univ.erase (0 : ZMod p), ((chiC b).re ^ 2) = (1 : ℝ) := by
      intro b hb
      have hbne : b ≠ 0 := (Finset.mem_erase.mp hb).1
      rcases quadraticChar_dichotomy hbne with h | h <;> simp [chiC_apply, h]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hcardE, nsmul_eq_mul, Nat.cast_sub hp1,
      Nat.cast_one, mul_one]
  have hC : ∑ b ∈ Finset.univ.erase (0 : ZMod p), 4 * τre ^ 2 * ((chiC b).re ^ 2)
      = 4 * τre ^ 2 * ((p : ℝ) - 1) := by
    rw [← Finset.mul_sum, hC1]
  rw [hA, hB, hC]; ring

end ArkLib.ProximityGap.QRExpSum

#print axioms ArkLib.ProximityGap.QRExpSum.tau_re_sq
#print axioms ArkLib.ProximityGap.QRExpSum.sum_term_eval
