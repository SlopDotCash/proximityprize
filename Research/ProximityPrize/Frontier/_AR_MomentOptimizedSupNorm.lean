/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentWickBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Moment-optimized sup-norm: `WickEnergyBound at all r` ⟹ explicit `M ≤ √(2e·n·(ln q + 1))` (#444)

`MomentWickBridge` proved the per-frequency ceiling: the depth-`r` Wick energy bound
`WickEnergyBound ψ G r` (`∑_{b≠0}‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ`) forces
`‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` for every `b≠0` (`eta_pow_le_of_wick`).  That left ONE elementary
real-analysis step — *optimizing the per-`r` ceiling over `r`* — to turn the family of power
bounds into the prize-shaped closed form `M ≤ √(c·n·ln q)`.  This file lands that step.

**The optimization (elementary).**  From `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` and the Stirling-free bound
`(2r−1)‼ = ∏_{i<r}(2i+1) ≤ (2r)ʳ` (`doubleFactOdd_le`):
* `‖η_b‖^{2r} ≤ q·(2r)ʳ·nʳ = q·(2nr)ʳ`, so taking the `r`-th root of the square,
  `‖η_b‖² = (‖η_b‖^{2r})^{1/r} ≤ q^{1/r}·(2nr)`.
* Choose the depth `r = ⌈ln q⌉` (`≥ 1` once `q ≥ e`).  Then `q^{1/r} = exp((ln q)/r) ≤ exp 1 = e`
  because `r ≥ ln q ≥ 0` ⟹ `(ln q)/r ≤ 1`.  Hence `‖η_b‖² ≤ 2e·n·r ≤ 2e·n·(ln q + 1)`.
* Taking square roots: `‖η_b‖ ≤ √(2e·n·(ln q + 1))` — the Gaussian/Ramanujan per-frequency target
  (`M ≤ √(c·n·ln q)` with `c = 2e ≈ 5.44`), matching the saddle constant.

So the metaplectic↔Wick chain is now a **full conditional consumer**: assuming
`∀ r, WickEnergyBound ψ G r` (the BGK/Paley √-cancellation wall — kept as the named hypothesis,
NEVER discharged at log depth), the prize per-frequency floor `M ≤ √(2e·n·(ln q+1))` follows by
this axiom-clean optimization.  The open content is *exactly* `WickEnergyBound` at `r ∼ ln q`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #444.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.MomentWickBridge

namespace ArkLib.ProximityGap.MomentOptimizedSupNorm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Stirling-free double-factorial bound.** `(2r−1)‼ = ∏_{i<r}(2i+1) ≤ (2r)ʳ`: each of the `r`
factors `2i+1` (`i < r`) is `≤ 2r`. -/
theorem doubleFactOdd_le (r : ℕ) : (doubleFactOdd r : ℝ) ≤ (2 * r : ℝ) ^ r := by
  have hcast : (doubleFactOdd r : ℝ) = ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ) := by
    unfold doubleFactOdd; push_cast; rfl
  rw [hcast]
  calc ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range r, (2 * r : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          have hir : i + 1 ≤ r := Finset.mem_range.mp hi
          have : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hir
          push_cast
          nlinarith [this]
    _ = (2 * r : ℝ) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- **The pure real-analysis optimization core.**  Given a nonnegative `B` with
`B^{2r} ≤ q·(2r)ʳ·nʳ` at depth `r = ⌈ln q⌉ ≥ 1`, `q ≥ 1`, `n ≥ 0`, conclude `B² ≤ 2·e·n·r`.
This is the `q^{1/r} ≤ e` saddle estimate, isolated from the Gauss-sum substrate. -/
theorem sq_le_of_pow_ceil {B q n : ℝ} (hB : 0 ≤ B) (hq : 1 ≤ q) (hn : 0 ≤ n)
    (r : ℕ) (hr : r = ⌈Real.log q⌉₊) (hr1 : 1 ≤ r)
    (hpow : B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r) :
    B ^ 2 ≤ 2 * Real.exp 1 * n * r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  -- `(B²)^r = B^{2r} ≤ q·(2nr)^r`
  have hkey : (B ^ 2) ^ r ≤ q * (2 * (n : ℝ) * r) ^ r := by
    rw [← pow_mul]
    calc B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r := hpow
      _ = q * (2 * n * r) ^ r := by
          rw [mul_pow, mul_pow]; ring
  -- take `r`-th root: `B² ≤ q^{1/r} · (2nr)`
  have hbase_nn : (0 : ℝ) ≤ 2 * (n : ℝ) * r := by positivity
  have hroot : B ^ 2 ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) := by
    calc B ^ 2 = ((B ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr1)).symm
      _ ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hkey (by positivity)
  -- factor the rpow: `(q · (2nr)^r)^{1/r} = q^{1/r} · (2nr)`
  have hsplit : (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by
    rw [Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (2 * (n : ℝ) * r) r, ← Real.rpow_mul hbase_nn]
    rw [mul_inv_cancel₀ hrne, Real.rpow_one]
  -- `q^{1/r} ≤ e` because `r ≥ ln q`
  have hlogq : Real.log q ≤ r := by
    rw [hr]; exact Nat.le_ceil _
  have hqr_le_e : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith) ((r : ℝ)⁻¹)]
    apply Real.exp_le_exp.mpr
    rw [mul_inv_le_iff₀ hrpos]
    calc Real.log q ≤ r := hlogq
      _ = 1 * r := (one_mul _).symm
  -- assemble
  calc B ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by rw [← hsplit]; exact hroot
    _ ≤ Real.exp 1 * (2 * (n : ℝ) * r) :=
        mul_le_mul_of_nonneg_right hqr_le_e hbase_nn
    _ = 2 * Real.exp 1 * n * r := by ring

/-- **The optimized per-frequency sup-norm bound (the prize-shaped closed form).**  Assuming the
Wick energy bound at the optimal depth `r = ⌈ln q⌉ ≥ 1`, every nonzero frequency obeys
`‖η_b‖² ≤ 2e·n·r ≤ 2e·n·(ln q + 1)`, hence `‖η_b‖ ≤ √(2e·n·(ln q + 1))`.  This is the full
Wick ⟹ floor consumer: the only open input is `WickEnergyBound ψ G ⌈ln q⌉`. -/
theorem eta_sq_le_optimized {ψ : AddChar F ℂ} (G : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickEnergyBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * r := by
  have hpow := eta_pow_le_of_wick (ψ := ψ) G r hwick hb
  -- rewrite the ceiling RHS through the `(2r)^r` double-factorial bound
  have hdf : (Fintype.card F : ℝ) * (doubleFactOdd r : ℝ) * (G.card : ℝ) ^ r
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := by
    have h1 : (doubleFactOdd r : ℝ) ≤ (2 * r : ℝ) ^ r := doubleFactOdd_le r
    have h2 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (G.card : ℝ) ^ r := by positivity
    nlinarith [h1, h2, h3, mul_nonneg h2 h3]
  have hpow' : ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := hpow.trans hdf
  exact sq_le_of_pow_ceil (norm_nonneg _) hq (by positivity) r hr hr1 hpow'

/-- **The prize floor, square-rooted.**  `‖η_b‖ ≤ √(2e·n·(ln q + 1))`.  Since `r = ⌈ln q⌉ < ln q + 1`
(`Nat.ceil_lt_add_one`), the depth-`r` ceiling collapses to a `q`-only closed form.  This is the
`M ≤ √(c·n·log q)` per-frequency target (`c = 2e`), conditional on `WickEnergyBound ψ G ⌈ln q⌉`. -/
theorem eta_le_sqrt_floor {ψ : AddChar F ℂ} (G : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwick : WickEnergyBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  have hsq := eta_sq_le_optimized (ψ := ψ) G r hr hr1 hq hwick hb
  -- bound `r < ln q + 1`
  have hlogq_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq
  have hrlt : (r : ℝ) < Real.log (Fintype.card F : ℝ) + 1 := by
    rw [hr]; exact Nat.ceil_lt_add_one hlogq_nn
  have hcoef_nn : (0 : ℝ) ≤ 2 * Real.exp 1 * (G.card : ℝ) := by positivity
  have hsq2 : ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1) := by
    calc ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * r := hsq
      _ ≤ 2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrlt.le hcoef_nn
  -- `‖η_b‖ = √(‖η_b‖²) ≤ √(RHS)`
  rw [show ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq2

end ArkLib.ProximityGap.MomentOptimizedSupNorm

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.MomentOptimizedSupNorm.doubleFactOdd_le
#print axioms ArkLib.ProximityGap.MomentOptimizedSupNorm.sq_le_of_pow_ceil
#print axioms ArkLib.ProximityGap.MomentOptimizedSupNorm.eta_sq_le_optimized
#print axioms ArkLib.ProximityGap.MomentOptimizedSupNorm.eta_le_sqrt_floor
