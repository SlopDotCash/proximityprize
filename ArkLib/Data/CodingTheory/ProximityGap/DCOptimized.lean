/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound

/-!
# The corrected, non-vacuous prize sup-norm bound (#407)

`GaussPeriodOptimizedBound.eta_le_optimized` derives `M ≤ √(2e·n·ln q)` from the in-tree
`GaussianEnergyBound` (`E_r ≤ Wick`) — which is **vacuous at the prize** (the DC term dominates, so the
hypothesis is false for `n ≥ 64`). This file gives the SAME conclusion from the **correct** DC-subtracted
hypothesis `DCEnergyBound` (`A_r ≤ Wick`, true at the prize):

> **`eta_sq_le_dcOptimized`** — from `DCEnergyBound G r` at `r ≥ max(1, ln q)`, for every `b ≠ 0`,
> `‖η_b‖² ≤ 2e·|G|·r`. At `r = ⌈ln q⌉`: the prize sup-norm `M ≤ √(2e·n·ln q)`, **non-vacuous**.

This is the corrected end-to-end conditional prize bound: the only open input is `A_r ≤ Wick`
(= the BGK / Anomaly-Suppression inequality), measured true at every prize prime.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.GaussPeriodOptimizedBound

namespace ArkLib.ProximityGap.DCOptimized

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Corrected optimized sup-norm bound.** From the DC-subtracted energy bound `DCEnergyBound G r` at
order `r ≥ max(1, ln q)`, every non-trivial Gauss period obeys `‖η_b‖² ≤ 2e·|G|·r`. At `r = ⌈ln q⌉` this
is the prize `M ≤ √(2e·n·ln q)` — and unlike the in-tree `eta_le_optimized`, the hypothesis is TRUE at
the prize parameters. -/
theorem eta_sq_le_dcOptimized {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (h : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set nc : ℝ := (G.card : ℝ) with hnc_def
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℕ) ≠ 0 := by omega
  have hqpos : 0 < q := by rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by positivity
  -- (‖η_b‖²)^r ≤ q·(2r−1)‼·nc^r   (from the DC hypothesis, b ≠ 0)
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r
      ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * nc ^ r := by
    rw [← pow_mul]
    have := eta_pow_le_of_dcEnergyBound hψ h hb
    rw [hq_def, hnc_def]; rw [← mul_assoc] at this; exact this
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

end ArkLib.ProximityGap.DCOptimized

#print axioms ArkLib.ProximityGap.DCOptimized.eta_sq_le_dcOptimized
