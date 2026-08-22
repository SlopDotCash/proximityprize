/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDeficitBudget
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Door-(iv) Lane-3: a SUB-`(log2)/2` average deficit cannot reach the √-scale via the exp budget (#444)

`_DoorIVDilationDeficitBudget` proved the deficit-budget bound `M a ≤ 2^a · exp(−S) · M 0`
(`S = ∑_{k<a} δ_k`) and that *certifying* the BGK prize target forces a **linear-in-`a`** budget.

This module records the matching **converse boundary**, sharpening "linear budget" into an explicit
per-level-average threshold on the *exp-relaxed* bound.  If the average per-level deficit is below
`ε* = (log 2)/2`, i.e. `S ≤ ε·a` with `ε < (log 2)/2`, then the budget bound's per-level factor
`2·exp(−ε)` strictly exceeds the prize per-level factor `√2`, so

> `(2·exp(−ε))^a > (√2)^a = √(2^a)` for `a ≥ 1`,

and the exp budget bound `2^a·exp(−S)·M 0 ≥ (2·exp(−ε))^a·M 0` stays **at or above** (strictly above
for `M 0 > 0`, `a ≥ 1`) the `√(2^a)·M 0` Plancherel/prize scale.  So the *exp-relaxed* budget can never
witness a `√n`-scale bound unless the average deficit reaches `(log 2)/2` — a sustained `Ω(1)`
per-level deficit.

(`(log 2)/2 ≈ 0.3466` is the EXP-relaxed threshold; the EXACT-product per-level threshold proven in
`_DoorIVUniformDeficitThreshold` is the smaller `(2−√2)/2 ≈ 0.2929`.  The two differ exactly because
`e^{−x} ≥ 1 − x` — the exp relaxation overcharges the deficit.  Both are linear-in-`a` floors.)

## What this module proves (and what it does NOT)

* `two_exp_neg_gt_sqrt2_of_lt` : `ε < (log 2)/2 ⟹ √2 < 2·exp(−ε)` (the per-level factor stays above `√2`).
* `sqrt2_pow_le_two_exp_neg_pow_of_le` : if `S ≤ ε·a` then `(√2)^a ≤ (2·exp(−ε))^a ≤ 2^a·exp(−S)`.
* `deficit_budget_ge_sqrt_scale_of_sublinear` : if `S ≤ ε·a` with `ε < (log 2)/2` and `M 0 ≥ 0`, then
  the budget bound is at or above the `√`-scale: `(√2)^a · M 0 ≤ 2^a · exp(−S) · M 0`.

It does **NOT** lower-bound the true `M(μ_n)` (that is the open CORE), and makes NO claim that any
deficit budget is or is not achievable.  It only states that *this particular bound* (the exp-relaxed
dilation budget) is at/above the `√`-scale whenever the average deficit is sub-`(log 2)/2`.  Lane-3
constraint lemma; CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetSublinearFloor

open Real

/-- **Per-level factor stays above `√2` below the exp threshold.**  If `ε < (log 2)/2` then
`√2 < 2·exp(−ε)`.  Proof by squaring (both sides nonneg): `(2·exp(−ε))² = 4·exp(−2ε) > 4·exp(−log 2)
= 4·(1/2) = 2 = (√2)²`, using `−2ε > −log 2` and `exp` monotone. -/
theorem two_exp_neg_gt_sqrt2_of_lt {ε : ℝ} (hε : ε < Real.log 2 / 2) :
    Real.sqrt 2 < 2 * Real.exp (-ε) := by
  have hrhs_pos : 0 < 2 * Real.exp (-ε) := by positivity
  -- compare squares
  have hsq : (Real.sqrt 2) ^ 2 < (2 * Real.exp (-ε)) ^ 2 := by
    have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hsqrt2_sq]
    -- (2 exp(-ε))² = 4 exp(-2ε)
    have hexp : (2 * Real.exp (-ε)) ^ 2 = 4 * Real.exp (-(2 * ε)) := by
      rw [mul_pow]
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hexp]
    -- 2 < 4 exp(-2ε) ⟺ 1/2 < exp(-2ε) ⟺ exp(-log2) < exp(-2ε) ⟺ -log2 < -2ε ⟺ 2ε < log2
    have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      norm_num
    have hmono : Real.exp (-Real.log 2) < Real.exp (-(2 * ε)) := by
      apply Real.exp_lt_exp.mpr
      linarith
    rw [hhalf] at hmono
    linarith
  -- squares strict + both nonneg ⟹ values strict
  nlinarith [Real.sqrt_nonneg 2, hrhs_pos, hsq]

/-- **Sub-average budget keeps the bound above the √-scale (power form).**  If `S ≤ ε·a` and
`ε < (log 2)/2`, then `(√2)^a ≤ (2·exp(−ε))^a ≤ 2^a·exp(−S)`.  The first inequality is the per-level
factor bound raised to the `a`-th power; the second uses `S ≤ ε·a ⟹ exp(−S) ≥ exp(−ε·a)` and
`(2·exp(−ε))^a = 2^a·exp(−ε·a)`. -/
theorem sqrt2_pow_le_two_exp_neg_pow_of_le {ε S : ℝ} (a : ℕ)
    (hε : ε < Real.log 2 / 2) (hS : S ≤ ε * a) :
    (Real.sqrt 2) ^ a ≤ 2 ^ a * Real.exp (-S) := by
  -- step 1: (√2)^a ≤ (2 exp(-ε))^a
  have hfac : Real.sqrt 2 ≤ 2 * Real.exp (-ε) := le_of_lt (two_exp_neg_gt_sqrt2_of_lt hε)
  have hsqrt2_nonneg : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : (Real.sqrt 2) ^ a ≤ (2 * Real.exp (-ε)) ^ a :=
    pow_le_pow_left₀ hsqrt2_nonneg hfac a
  -- (2 exp(-ε))^a = 2^a exp(-ε a)
  have h2 : (2 * Real.exp (-ε)) ^ a = 2 ^ a * Real.exp (-(ε * a)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  -- exp(-ε a) ≤ exp(-S) since S ≤ ε a ⟹ -ε a ≤ -S
  have h3 : Real.exp (-(ε * a)) ≤ Real.exp (-S) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow_nonneg : (0:ℝ) ≤ (2:ℝ) ^ a := by positivity
  calc (Real.sqrt 2) ^ a ≤ (2 * Real.exp (-ε)) ^ a := h1
    _ = 2 ^ a * Real.exp (-(ε * a)) := h2
    _ ≤ 2 ^ a * Real.exp (-S) := mul_le_mul_of_nonneg_left h3 hpow_nonneg

/-- **The exp budget bound stays at/above the √-scale under a sub-`(log2)/2` average deficit.**  If the
total deficit budget is sub-average `S ≤ ε·a` with `ε < (log 2)/2`, then for `M 0 ≥ 0` the
deficit-budget bound is at least the `√(2^a)·M 0` Plancherel scale:
`(√2)^a · M 0 ≤ 2^a · exp(−S) · M 0`.  Hence the *exp-relaxed* dilation budget cannot witness a
`√n`-scale bound unless the average per-level coherence deficit reaches `(log 2)/2` — a sustained
`Ω(1)` deficit, the linear-in-`a` floor.  Lane-3 constraint lemma; CORE not discharged. -/
theorem deficit_budget_ge_sqrt_scale_of_sublinear {ε S M0 : ℝ} (a : ℕ)
    (hε : ε < Real.log 2 / 2) (hS : S ≤ ε * a) (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0 ≤ 2 ^ a * Real.exp (-S) * M0 := by
  have h := sqrt2_pow_le_two_exp_neg_pow_of_le a hε hS
  exact mul_le_mul_of_nonneg_right h hM0

end ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetSublinearFloor
