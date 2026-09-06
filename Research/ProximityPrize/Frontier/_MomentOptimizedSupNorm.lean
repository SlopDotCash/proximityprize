/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# LANE M (#466 R13): `WallHolds ⟹ M ≤ √(2e·n·(ln q + 1))` — the moment-order optimization,
  routed through the DC-subtracted wall (removing the un-formalized parameter from the capstone)

The `_WallCapstone.lean` capstone (round 12) certifies `WallHolds ⟹ per-rung Wick bound`
axiom-clean, but leaves ONE step un-formalized (caveat (a)): the **moment-order optimization** that
turns the family of `2r`-power bounds `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` (one per rung `r`) into a single
sup-norm `M ≤ C·√(n·ln q)`.  It therefore passed `B`/`hB` as a *parameter*.

This file lands that step **directly from `WallHolds`** (via the DC-subtracted
`DCEnergyCorrection.eta_pow_le_of_dcEnergyBound`, non-vacuous at the prize), producing the
axiom-clean statement

> **`eta_le_sqrt_floor_of_wallHolds`** :
>   `WallHolds G` ⟹ for every `b ≠ 0`, `‖η_b‖ ≤ √(2e·n·(ln q + 1))`

and its `∀-b` sup-norm corollary `supNorm_le_of_wallHolds`.  This is the round-12 caveat (a) removed:
the wall now discharges the *closed-form* per-frequency sup-norm bound `M ≤ C·√(n·ln q)` (with
`C = √(2e)`), not merely the per-rung inputs.

## The optimization (elementary real analysis, isolated in `sq_le_of_pow_ceil`)

From the per-rung wall bound `‖η_b‖^{2r} ≤ q·(2r−1)‼·nʳ` and the Stirling-free
`(2r−1)‼ ≤ (2r)ʳ`:

* `‖η_b‖^{2r} ≤ q·(2nr)ʳ`, so taking the `r`-th root of the square,
  `‖η_b‖² ≤ q^{1/r}·(2nr)`.
* Choose the depth `r = ⌈ln q⌉` (`≥ 1` once `q ≥ e`).  Then `q^{1/r} = exp((ln q)/r) ≤ e`
  because `r ≥ ln q`.  Hence `‖η_b‖² ≤ 2e·n·r ≤ 2e·n·(ln q + 1)`.
* Square roots: `‖η_b‖ ≤ √(2e·n·(ln q + 1))` — the Gaussian/Ramanujan per-frequency target
  (`M ≤ √(c·n·ln q)`, `c = 2e ≈ 5.44`).

## The load-bearing new lemma

The DC-subtracted wall uses the **Mathlib** double factorial `Nat.doubleFactorial (2r−1)` (whereas
`MomentWickBridge` used the project-local `doubleFactOdd`).  The one genuinely new arithmetic input
here is `doubleFactorial_two_sub_one_le` : `((2r−1)‼ : ℝ) ≤ (2r)ʳ`, proved for the Mathlib object
from `doubleFactorial_le_factorial` and `Nat.factorial_le_pow`-style monotonicity.  Everything else
is the isolated saddle estimate `sq_le_of_pow_ceil`, re-derived here so the file depends only on
`DCEnergyCorrection` (no import of the `WickEnergyBound`/`doubleFactOdd` route).

## Honest scope

* `WallHolds G := ∀ r, DCEnergyBound G r` is the SAME object as in `_WallCapstone`; it is **not**
  discharged — it is the named open wall, consumed as a hypothesis.
* The conclusion `‖η_b‖ ≤ √(2e·n·(ln q+1))` is a **conditional** on `WallHolds`, axiom-clean.
* `C = √(2e)` is the crude saddle constant from the `(2r−1)‼ ≤ (2r)ʳ` bound at `r = ⌈ln q⌉`.  Probe
  `probe_466r13_moment.py` measures the *true* optimized-Wick constant ≈ `1.43·√(n ln q)` (a sharper
  argmin near `r ≈ ln q`); the `√(2e) ≈ 2.33` here is an honest over-estimate of that, sufficient for
  the order `√(n·ln q)`.  The sharper constant is left as a probe-validated numeric, not claimed as a
  Lean theorem.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 13, LANE M.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The new arithmetic input: `((2r−1)‼ : ℝ) ≤ (2r)ʳ` for the Mathlib double factorial. -/

/-- **Stirling-free bound on the Mathlib odd double factorial.**  `(2r−1)‼ ≤ (2r)ʳ`.

For `r ≥ 1`, `(2r−1)‼ = 1·3·5···(2r−1)` is a product of `r` factors each `≤ 2r`; for `r = 0`,
`(2·0−1)‼ = 0‼ = 1 = (2·0)⁰` (nat subtraction makes `2·0−1 = 0`).  We prove it via the closed form
`(2r−1)‼ = ∏_{i<r}(2i+1)` (derived from `Nat.doubleFactorial_eq_prod_odd`) and factorwise
monotonicity — the same argument as `MomentWickBridge.doubleFactOdd_le`, transported to the Mathlib
object. -/
theorem doubleFactorial_two_sub_one_le (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ (2 * r : ℝ) ^ r := by
  -- closed form: `(2r−1)‼ = ∏_{i<r}(2i+1)` (as naturals)
  have hclosed : Nat.doubleFactorial (2 * r - 1) = ∏ i ∈ Finset.range r, (2 * i + 1) := by
    cases r with
    | zero => simp
    | succ m =>
      -- `2(m+1) − 1 = 2m + 1`; use `doubleFactorial_eq_prod_odd m : (2m+1)‼ = ∏_{i<m}(2(i+1)+1)`
      have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [h2, Nat.doubleFactorial_eq_prod_odd m]
      -- `∏_{i<m}(2(i+1)+1) = ∏_{i∈range(m+1)}(2i+1)`: the `i=0` factor is `1`, and shifting
      rw [Finset.prod_range_succ']
      simp
  have hcast : (Nat.doubleFactorial (2 * r - 1) : ℝ)
      = ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ) := by
    rw [hclosed]; push_cast; rfl
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

/-! ### (1) The isolated saddle estimate `q^{1/r} ≤ e` at `r = ⌈ln q⌉`. -/

/-- **The pure real-analysis optimization core.**  Given nonnegative `B` with
`B^{2r} ≤ q·(2r)ʳ·nʳ` at depth `r = ⌈ln q⌉ ≥ 1`, `q ≥ 1`, `n ≥ 0`, conclude `B² ≤ 2·e·n·r`.
This is the `q^{1/r} ≤ e` saddle estimate, isolated from the Gauss-sum substrate.  (Same statement
as `MomentOptimizedSupNorm.sq_le_of_pow_ceil`, re-proved here to keep this file's dependency to
`DCEnergyCorrection` only.) -/
theorem sq_le_of_pow_ceil {B q n : ℝ} (hB : 0 ≤ B) (hq : 1 ≤ q) (hn : 0 ≤ n)
    (r : ℕ) (hr : r = ⌈Real.log q⌉₊) (hr1 : 1 ≤ r)
    (hpow : B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r) :
    B ^ 2 ≤ 2 * Real.exp 1 * n * r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hkey : (B ^ 2) ^ r ≤ q * (2 * (n : ℝ) * r) ^ r := by
    rw [← pow_mul]
    calc B ^ (2 * r) ≤ q * (2 * r : ℝ) ^ r * n ^ r := hpow
      _ = q * (2 * n * r) ^ r := by
          rw [mul_pow, mul_pow]; ring
  have hbase_nn : (0 : ℝ) ≤ 2 * (n : ℝ) * r := by positivity
  have hroot : B ^ 2 ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) := by
    calc B ^ 2 = ((B ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr1)).symm
      _ ≤ (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hkey (by positivity)
  have hsplit : (q * (2 * (n : ℝ) * r) ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by
    rw [Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (2 * (n : ℝ) * r) r, ← Real.rpow_mul hbase_nn]
    rw [mul_inv_cancel₀ hrne, Real.rpow_one]
  have hlogq : Real.log q ≤ r := by
    rw [hr]; exact Nat.le_ceil _
  have hqr_le_e : q ^ ((r : ℝ)⁻¹) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by linarith) ((r : ℝ)⁻¹)]
    apply Real.exp_le_exp.mpr
    rw [mul_inv_le_iff₀ hrpos]
    calc Real.log q ≤ r := hlogq
      _ = 1 * r := (one_mul _).symm
  calc B ^ 2 ≤ q ^ ((r : ℝ)⁻¹) * (2 * (n : ℝ) * r) := by rw [← hsplit]; exact hroot
    _ ≤ Real.exp 1 * (2 * (n : ℝ) * r) :=
        mul_le_mul_of_nonneg_right hqr_le_e hbase_nn
    _ = 2 * Real.exp 1 * n * r := by ring

/-! ### (2) The per-rung wall bound, ceiling-rewritten to the `(2r)ʳ` form. -/

/-- **The per-frequency `2r`-power bound from `WallHolds`, in the `(2r)ʳ` form.**  From the wall
`DCEnergyBound G r` (via `eta_pow_le_of_dcEnergyBound`) and `(2r−1)‼ ≤ (2r)ʳ`, every nonzero
frequency obeys `‖η_b‖^{2r} ≤ q·(2r)ʳ·nʳ`.  This is exactly the hypothesis `sq_le_of_pow_ceil`
consumes. -/
theorem eta_pow_le_wall_form {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hr : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := by
  have hpow := eta_pow_le_of_dcEnergyBound hψ hr hb
  -- `q·((2r−1)‼·nʳ) ≤ q·((2r)ʳ·nʳ) = q·(2r)ʳ·nʳ`
  have hdf : (Fintype.card F : ℝ)
        * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := by
    have h1 : (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ (2 * r : ℝ) ^ r :=
      doubleFactorial_two_sub_one_le r
    have h2 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (G.card : ℝ) ^ r := by positivity
    nlinarith [h1, h2, h3, mul_nonneg h2 h3]
  exact hpow.trans hdf

/-! ### (3) The main conditional: `WallHolds ⟹ ‖η_b‖ ≤ √(2e·n·(ln q + 1))`. -/

/-- **`WallHolds ⟹ per-frequency sup-norm squared bound at the optimal rung.**  Assuming the wall
`DCEnergyBound G ⌈ln q⌉` at the moment-optimal depth `r = ⌈ln q⌉ ≥ 1`, every nonzero frequency
obeys `‖η_b‖² ≤ 2e·n·r`.  Combines `eta_pow_le_wall_form` with the saddle estimate
`sq_le_of_pow_ceil`. -/
theorem eta_sq_le_optimized_of_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwall : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * r := by
  have hpow := eta_pow_le_wall_form hψ hwall hb
  exact sq_le_of_pow_ceil (norm_nonneg _) hq (by positivity) r hr hr1 hpow

/-- **The prize floor from `WallHolds` (per rung `= ⌈ln q⌉`), square-rooted.**  Assuming the wall at
the optimal depth `r = ⌈ln q⌉`, `‖η_b‖ ≤ √(2e·n·(ln q + 1))` for every `b ≠ 0`.  Since
`r = ⌈ln q⌉ < ln q + 1`, the depth-`r` ceiling collapses to a `q`-only closed form.  This is the
`M ≤ √(c·n·log q)` per-frequency target (`c = 2e`), conditional on the DC-subtracted wall
`DCEnergyBound G ⌈ln q⌉`. -/
theorem eta_le_sqrt_floor_of_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hr : r = ⌈Real.log (Fintype.card F : ℝ)⌉₊) (hr1 : 1 ≤ r)
    (hq : 1 ≤ (Fintype.card F : ℝ))
    (hwall : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  have hsq := eta_sq_le_optimized_of_dc hψ G r hr hr1 hq hwall hb
  have hlogq_nn : 0 ≤ Real.log (Fintype.card F : ℝ) := Real.log_nonneg hq
  have hrlt : (r : ℝ) < Real.log (Fintype.card F : ℝ) + 1 := by
    rw [hr]; exact Nat.ceil_lt_add_one hlogq_nn
  have hcoef_nn : (0 : ℝ) ≤ 2 * Real.exp 1 * (G.card : ℝ) := by positivity
  have hsq2 : ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1) := by
    calc ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * r := hsq
      _ ≤ 2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrlt.le hcoef_nn
  rw [show ‖eta ψ G b‖ = Real.sqrt (‖eta ψ G b‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hsq2

/-! ### (4) The `WallHolds`-level statement: the wall (∀-r) discharges the closed-form sup-norm. -/

/-- **`WallHolds` reference.**  For a multiplicative subgroup `G = μ_n ⊆ F^*`, the wall is
`∀ r, DCEnergyBound G r` — the SAME object as `Frontier.WallCapstone.WallHolds`.  Restated here so
the closed-form consumer below can be stated against it without importing the capstone (avoiding a
cycle: the capstone imports this file's route conceptually). -/
def WallHolds (G : Finset F) : Prop := ∀ r : ℕ, DCEnergyBound G r

/-- **THE LANE-M RESULT (axiom-clean): `WallHolds ⟹ M ≤ √(2e·n·(ln q + 1))`.**  The whole
moment-order optimization, discharged directly from the DC-subtracted wall.  For a smooth subgroup
`G = μ_n` with `|F| = q ≥ e` (so `⌈ln q⌉ ≥ 1`), assuming `WallHolds G`, every nonzero Gauss period
obeys the prize-shaped closed-form sup-norm bound `‖η_b‖ ≤ √(2e·n·(ln q + 1))`.

This is the round-12 caveat (a) REMOVED: the wall no longer merely supplies the per-rung inputs to
an un-formalized optimization — it discharges the closed-form per-frequency sup-norm `M ≤ C·√(n·ln q)`
(`C = √(2e)`) axiom-clean.  The only open input is `WallHolds` (the wall), unchanged. -/
theorem eta_le_of_wallHolds {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hwall : WallHolds G) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖
      ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) := by
  set r := ⌈Real.log (Fintype.card F : ℝ)⌉₊ with hrdef
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hq
  -- `ln q ≥ 1` (since `q ≥ e`), so `⌈ln q⌉ ≥ 1`
  have hlog_ge_one : 1 ≤ Real.log (Fintype.card F : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hq
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    exact Nat.one_le_ceil_iff.mpr (by linarith)
  exact eta_le_sqrt_floor_of_dc hψ G r hrdef hr1 hq1 (hwall r) hb

/-- **The sup-norm corollary: `WallHolds ⟹ M := max_{b≠0} ‖η_b‖ ≤ √(2e·n·(ln q + 1))`.**  A uniform
`∀ b ≠ 0` restatement of `eta_le_of_wallHolds` — the object `M(n)` the whole BGK/Paley wall controls,
now bounded by the closed form conditional on the wall.  This is exactly the `B`/`hB` parameter that
`_WallCapstone.wall_capstone` passed in: LANE M supplies it from `WallHolds`. -/
theorem supNorm_le_of_wallHolds {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ)) (hwall : WallHolds G) :
    ∀ b : F, b ≠ 0 →
      ‖eta ψ G b‖
        ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  fun b hb => eta_le_of_wallHolds hψ G hq hwall hb

/-- **Non-negativity of the closed-form bound** — trivial, recorded so downstream consumers
(`le_mcaDeltaStar_of_charSumBound`, which needs `0 ≤ B`) can instantiate `B` with the LANE-M
sup-norm without re-deriving it. -/
theorem sqrt_floor_nonneg (G : Finset F) :
    (0 : ℝ) ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)) :=
  Real.sqrt_nonneg _

end ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.doubleFactorial_two_sub_one_le
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.sq_le_of_pow_ceil
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.eta_pow_le_wall_form
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.eta_sq_le_optimized_of_dc
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.eta_le_sqrt_floor_of_dc
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.eta_le_of_wallHolds
#print axioms ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.supNorm_le_of_wallHolds
