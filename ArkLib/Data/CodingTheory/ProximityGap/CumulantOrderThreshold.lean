/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CumulantGaussPeriodBound

/-!
# The cumulant-order threshold: the moment method needs `r > log q / log n` (#407)

This file lands the **quantitative form** of the low-order obstruction found in the
2026-06-14 "BGK ceiling fresh angle" pass.  It makes precise *why* the moment / cumulant route
(`CumulantGaussPeriodBound.lean`) cannot produce a sub-trivial per-frequency bound unless it is
run at order `r > log_n q`.  It does **not** show that the analytic input `CumulantEnergyBound`
fails at those higher orders: whether that DC-subtracted input holds at a given useful order is a
separate, characteristic/subgroup-specific question (see the correction below).

## The extracted bound and its `q`-prefactor floor

The cumulant consumer `worstCaseIncompleteSumBound_of_cumulantBound` discharges the open residual
`WorstCaseIncompleteSumBound ψ G M_r²` with

  `M_r² = (q · (2r-1)‼ · n^r)^{1/r}   =   q^{1/r} · ((2r-1)‼)^{1/r} · n`

(`n = |G|`, `q = |F|`).  Because `(2r-1)‼ ≥ 1`, this is **bounded below** by

  `M_r²  ≥  q^{1/r} · n`,                               (`cumulant_extract_ge`)

so the extracted *square* `M_r²` exceeds the trivial value `n²` (i.e. `M_r ≥ n`, no improvement
over `‖η_b‖ ≤ |G| = n`) whenever `q^{1/r} ≥ n`, i.e. whenever

  `r  ≤  log q / log n`.                                (`cumulant_no_gain_of_small_order`)

Equivalently: **the moment method can beat the trivial bound only at order `r > log_n q`.**  At
the prize point (`q = 2¹⁵⁸`, `n = 2³⁰`) this threshold is `log_n q ≈ 5.27`; the optimum order for
the *target* `√(n log(q/n))` is `r ≈ log(q/n) ≈ 64–128`.

**Correction (no "disjoint regimes" theorem).**  An earlier version of this docstring argued that
`CumulantEnergyBound` (`q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`) forces `n^{2r}/q ≤ (2r-1)‼·n^r`, hence
`r ≲ log_n q`, so that the *useful* and *valid* orders would be disjoint.  That implication is
false: the subtraction of `n^{2r}` removes exactly that DC mass, so the cumulant input carries no
such guard.  (The guard does apply to the raw, un-subtracted `GaussianEnergyBound`.)  Concrete
proper-subgroup counterexample: `F_17`, `G = μ_8 = {1,2,4,8,9,13,15,16}`, `r = 2`.  Exact
enumeration gives `E_2 = 264`, so `q·E_2 − n⁴ = 17·264 − 4096 = 392 ≤ 17·3·64 = 3264`, i.e.
`CumulantEnergyBound G 2` holds, although `n² = 64 > 17·3 = 51` (the raw Wick bound fails the DC
guard).  Its extracted square is `√3264 < 64 = n²`, a genuine gain at the useful order
`r = 2 > log_8 17`.  So useful orders with a valid DC-subtracted input do exist; any failure of
`CumulantEnergyBound` at useful orders must be established separately for the relevant
characteristic and subgroup (e.g. the measured excess fed to `not_cumulantBound_of_excess`).

## What is proven here (axiom-clean)

* `cumulant_extract_ge` — the `q^{1/r}·n` lower bound on the extracted square `M_r²` (the
  `q`-prefactor floor; `(2r-1)‼ ≥ 1` is the only structural input).
* `cumulant_no_gain_of_small_order` — if `n^r ≤ q` (i.e. `r ≤ log_n q`) then `M_r² ≥ n²`, so the
  cumulant extraction gives **no** improvement over the trivial `‖η_b‖ ≤ |G|`.  This is the formal
  statement that the moment method must be run at order `r > log_n q` to gain anything.

These are *unconditional* facts about the extraction formula (no hypothesis on `E_r` at all): they
hold whether or not `CumulantEnergyBound` is true.  They say nothing about whether
`CumulantEnergyBound` holds at orders `r > log_n q`.  `not_cumulantBound_of_excess` is only a
falsification hook: it refutes `CumulantEnergyBound` at an order `r` *given* a measured excess at
that `r` (the probe reports such excesses at the Fermat prime `p = 65537`, `n = 64`, `r = 2..5`);
it is not a theorem that the input fails at every order above `log_n p`, and the `F_17`, `μ_8`
example above shows the input can hold at a useful order.

**Honest scope.**  This does NOT bound `M`.  It is a *no-go* for the moment route at low order
(`r ≤ log_n q`) only; it does not prove that the useful and valid orders are disjoint.  The open
core is
unchanged: an unconditional `M ≤ C√(n log(q/n))` at the prize point (BGK / Paley, the `n^{1-c} →
n^{1/2+o(1)}` gap for thin multiplicative subgroups).  Axiom target `[propext, Classical.choice,
Quot.sound]`.  Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.CumulantOrderThreshold

set_option linter.style.longLine false

variable {F : Type*} [Fintype F]

/-- `(2r-1)‼ ≥ 1` as a real number (the double factorial is a positive integer). -/
theorem one_le_doubleFactorial_real (r : ℕ) :
    (1 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
  have h : 1 ≤ Nat.doubleFactorial (2 * r - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact_mod_cast h

/-- **The `q`-prefactor floor on the extracted square.** The cumulant consumer's bound parameter
`M_r² = (q · (2r-1)‼ · n^r)^{1/r}` is bounded **below** by `q^{1/r} · n`, because `(2r-1)‼ ≥ 1`.
This is the structural reason the moment method carries an irreducible `q^{1/r}` cost: the
far-frequency mass is normalised by the *full* field size `q`, and extracting a single frequency at
order `r` only divides that back out as a `1/r`-power. -/
theorem cumulant_extract_ge {r : ℕ} (hr : 1 ≤ r)
    (hq : (0 : ℝ) ≤ Fintype.card F) {G : Finset F} :
    (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) * (G.card : ℝ)
      ≤ ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹) := by
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  have hGnn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  -- `q^{1/r} · n = q^{1/r} · (n^r)^{1/r} = (q · n^r)^{1/r} ≤ (q · (2r-1)‼ · n^r)^{1/r}`.
  have hn_eq : (G.card : ℝ) = ((G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast ((G.card : ℝ)) r, ← Real.rpow_mul hGnn,
      mul_inv_cancel₀ hrne, Real.rpow_one]
  have hpowrnn : (0 : ℝ) ≤ (G.card : ℝ) ^ r := pow_nonneg hGnn r
  have hstep1 : (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) * (G.card : ℝ)
      = ((Fintype.card F : ℝ) * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹) := by
    rw [hn_eq, ← Real.mul_rpow hq hpowrnn]
    congr 2
    rw [← hn_eq]
  rw [hstep1]
  -- monotonicity of `x ↦ x^{1/r}` and `q · n^r ≤ q · (2r-1)‼ · n^r`.
  apply Real.rpow_le_rpow (mul_nonneg hq hpowrnn) _ hrinv
  have hdf : (1 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) := one_le_doubleFactorial_real r
  nlinarith [mul_nonneg hq hpowrnn, hpowrnn, hq]

/-- **No gain at low order.** If `n^r ≤ q` (equivalently `r ≤ log_n q`), then the cumulant-extracted
bound parameter `M_r²` is `≥ n²`, i.e. `M_r ≥ n`: the moment method gives **no** improvement over the
trivial `‖η_b‖ ≤ |G| = n` at any order `r ≤ log_n q`.  To beat the trivial bound the method must be
run at order `r > log_n q` — which at the prize (`q = 2¹⁵⁸`, `n = 2³⁰`) is `> 5.27`.  Unconditional
in `E_r`; whether `CumulantEnergyBound` holds at a given order `r > log_n q` is not addressed here
(it can, e.g. `F_17`, `G = μ_8`, `r = 2`; see the module docstring). -/
theorem cumulant_no_gain_of_small_order {r : ℕ} (hr : 1 ≤ r)
    {G : Finset F} (hq : (0 : ℝ) ≤ Fintype.card F)
    (hsmall : (G.card : ℝ) ^ r ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) ^ 2
      ≤ ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹) := by
  have hGnn : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  have hrinv : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
  have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  -- From `n^r ≤ q`: `n ≤ q^{1/r}`, hence `n² = n·n ≤ q^{1/r}·n ≤ M_r²`.
  have hn_le : (G.card : ℝ) ≤ (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) := by
    have h1 : ((G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹) ≤ (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) :=
      Real.rpow_le_rpow (pow_nonneg hGnn r) hsmall hrinv
    rwa [← Real.rpow_natCast ((G.card : ℝ)) r, ← Real.rpow_mul hGnn,
      mul_inv_cancel₀ hrne, Real.rpow_one] at h1
  calc (G.card : ℝ) ^ 2
      = (G.card : ℝ) * (G.card : ℝ) := by ring
    _ ≤ (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) * (G.card : ℝ) :=
        mul_le_mul_of_nonneg_right hn_le hGnn
    _ ≤ ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          ^ ((r : ℝ)⁻¹) := cumulant_extract_ge hr hq

end ArkLib.ProximityGap.CumulantOrderThreshold
