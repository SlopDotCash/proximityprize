/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The optimized Gauss-period bound `‖η_b‖ ≤ √(2e · n · ln q)` (#407)

`GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound` proves the **per-order**
moment bound `‖η_b‖² ≤ (q·(2r-1)‼·n^r)^{1/r}` from `GaussianEnergyBound G r`, and its docstring
notes that *minimizing over `r` (optimum `r* ≈ ln q`) yields the `√(2 n ln q)` Gauss-period bound*.
This file machine-checks that final optimization step, which was previously only stated informally.

The closed form is the prize sup-norm target up to the constant: choosing any order `r ≥ ln q`
collapses the field-size factor `q^{1/r} ≤ e`, and the crude factorial estimate
`(2r-1)‼ ≤ (2r)^r` gives `((2r-1)‼)^{1/r} ≤ 2r`, so

> `‖η_b‖² ≤ e · 2r · n = 2e · n · r`,  hence at `r = ⌈ln q⌉`:  `‖η_b‖ ≤ √(2e) · √(n · ln q)`.

This is **conditional on `GaussianEnergyBound G r`** — the proven char-0 / small-`n` input whose
char-`p` transfer at the prize parameters (`n = 2^μ`, `q ≈ n^4`, `r ≈ ln q`) is the single open
residual (= the BGK / Paley square-root-cancellation wall; see `EffectiveTransfer.lean` for the
proven regime `q > (2r)^{n/2}`).  It does **not** prove that input; it formalizes the elementary
implication `GaussianEnergyBound at r ≈ ln q ⟹ √-cancellation sup-norm`, pinning the constant.

The sharp constant `√2` needs Stirling `(2r-1)‼ ∼ √2·(2r/e)^r`; the crude `(2r)^r` here yields
`√(2e) ≈ 2.33` in its place — same shape, an explicit absolute constant.

Issue #407.
-/

open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.GaussPeriodOptimizedBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Crude double-factorial estimate.** `(2r-1)‼ ≤ (2r)^r`: a product of `r` odd factors each
`≤ 2r`. -/
theorem doubleFactorial_le_pow (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ r := by
  rcases r with _ | k
  · simp [Nat.doubleFactorial]
  · have hnat : Nat.doubleFactorial (2 * (k + 1) - 1) ≤ (2 * (k + 1)) ^ (k + 1) := by
      have he : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [he, Nat.doubleFactorial_eq_prod_odd k]
      calc ∏ i ∈ Finset.range k, (2 * (i + 1) + 1)
          ≤ (2 * (k + 1)) ^ (Finset.range k).card :=
            Finset.prod_le_pow_card _ _ _ (by intro i hi; simp only [Finset.mem_range] at hi; omega)
        _ = (2 * (k + 1)) ^ k := by rw [Finset.card_range]
        _ ≤ (2 * (k + 1)) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ)
        ≤ (((2 * (k + 1)) ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((2 * (k + 1) : ℕ) : ℝ) ^ (k + 1) := by push_cast; ring

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-- **Field-size collapse.** For `0 < q` and any order `r ≥ log q` (`r > 0`), the field-size
factor `q^{1/r} ≤ e`.  This is what makes `r ≈ ln q` the optimal moment order. -/
theorem rpow_inv_le_exp_one {q : ℝ} (hq : 0 < q) {r : ℝ} (hr : 0 < r) (hrq : Real.log q ≤ r) :
    q ^ (r⁻¹) ≤ Real.exp 1 := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  have : Real.log q * r⁻¹ ≤ r * r⁻¹ :=
    mul_le_mul_of_nonneg_right hrq (le_of_lt (inv_pos.mpr hr))
  rwa [mul_inv_cancel₀ (ne_of_gt hr)] at this

/-- **The optimized Gauss-period bound (squared form).**  From `GaussianEnergyBound G r` at any
order `r ≥ max(1, log q)`, every Gauss period satisfies `‖η_b‖² ≤ 2e · |G| · r`.  Taking the
optimal `r = ⌈ln q⌉` gives `‖η_b‖² ≤ 2e · |G| · ⌈ln q⌉`, the square-root-cancellation scale
`‖η_b‖ = O(√(|G| · ln q))` with the explicit constant `√(2e)`.

Conditional on `GaussianEnergyBound` (proven char-0, and in `F_q` whenever `q > (2r)^{|G|/2}`);
its char-`p` transfer at the prize parameters is the single open BGK residual. -/
theorem eta_sq_le_optimized {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : GaussianEnergyBound G r) (b : F) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set nc : ℝ := (G.card : ℝ) with hnc_def
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : 0 < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r := by
    rw [← pow_mul]; exact eta_pow_le_of_energyBound hψ h b
  -- ‖η‖² ≤ X^{1/r}, then expand the rpow over the product
  have hstep1 : ‖eta ψ G b‖ ^ 2
      ≤ (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r) ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (by positivity)
  have hexpand : (q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (le_of_lt hqpos) hd0,
        Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ nc) hrne]
  rw [hexpand] at hstep1
  have hbq : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := rpow_inv_le_exp_one hqpos hr0 hrq
  have hbd : (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) ≤ 2 * (r : ℝ) := by
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
        ≤ (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow hd0 (doubleFactorial_le_pow r) (by positivity)
      _ = ((2 * r : ℕ) : ℝ) := Real.pow_rpow_inv_natCast (by positivity) hrne
      _ = 2 * (r : ℝ) := by push_cast; ring
  calc ‖eta ψ G b‖ ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹) * nc := hstep1
    _ ≤ Real.exp 1 * (2 * (r : ℝ)) * nc := by gcongr
    _ = 2 * Real.exp 1 * nc * (r : ℝ) := by ring

/-- **The optimized Gauss-period bound (norm form).**  `‖η_b‖ ≤ √(2e · |G| · r)` — the
square-root-cancellation sup-norm, conditional on `GaussianEnergyBound G r` at `r ≥ max(1,log q)`.
At `r = ⌈ln q⌉` this is `‖η_b‖ ≤ √(2e · |G| · ln q)(1+o(1))`, the prize target up to the constant
`√(2e)` (the sharp `√2` needs Stirling in place of the crude `(2r-1)‼ ≤ (2r)^r`). -/
theorem eta_le_optimized {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r)
    (hrq : Real.log (Fintype.card F) ≤ r) (h : GaussianEnergyBound G r) (b : F) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := by
  have hsq := eta_sq_le_optimized hψ hr hrq h b
  calc ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) := Real.sqrt_le_sqrt hsq

end ArkLib.ProximityGap.GaussPeriodOptimizedBound

#print axioms ArkLib.ProximityGap.GaussPeriodOptimizedBound.eta_sq_le_optimized
#print axioms ArkLib.ProximityGap.GaussPeriodOptimizedBound.eta_le_optimized
