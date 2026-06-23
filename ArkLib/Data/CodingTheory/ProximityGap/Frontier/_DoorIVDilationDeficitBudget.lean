/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentTelescope
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) Lane-3: the VARIABLE-per-level dilation telescope and its coherence-deficit budget (#444)

`_DoorIVDilationDescentTelescope` telescoped the 2-dilation descent with a *constant* per-level factor:
`telescope_per_level_factor` gives `M a ≤ c^a · M 0` when every level obeys `M(k+1) ≤ c·M k` for one
fixed `c`.  But the per-level factor is **not** constant: `_DoorIVDilationFactorCoherenceWeld` proved
the level-`k` factor is `c_k ≤ 2 − 2·δ_k`, where `δ_k ∈ [0,1]` is the level-`k` coherence deficit
`1 − ρ_k` — a quantity that *varies per level*.  No file telescoped a **variable** per-level factor,
nor converted the resulting product `∏_k (2 − 2δ_k)` into an additive deficit *budget*.

This module supplies exactly that missing cross-link, as a kernel-checked Lane-3 constraint lemma.

## What this module proves (and what it does NOT)

For a nonnegative level-indexed worst-period sequence `M : ℕ → ℝ` and a per-level deficit sequence
`δ : ℕ → ℝ` with `δ_k ∈ [0,1]`:

* `telescope_variable_factor` — the **variable** per-level telescope:
  if `M(k+1) ≤ (2 − 2·δ k)·M k` for every `k < a`, then `M a ≤ (∏_{k<a} (2 − 2·δ k)) · M 0`.
* `prod_two_sub_two_deficit_eq` — the algebraic split `∏_{k<a}(2 − 2δ_k) = 2^a · ∏_{k<a}(1 − δ_k)`.
* `prod_one_sub_le_exp_neg_sum` — the **multiplicative→additive** engine
  `∏_{k<a}(1 − δ_k) ≤ exp(−∑_{k<a} δ_k)` (pointwise `1 − x ≤ e^{−x}` + product monotonicity).
* `telescope_deficit_budget` — the **headline budget bound**:
  `M a ≤ 2^a · exp(−∑_{k<a} δ_k) · M 0`.
  So the dilation descent converts the trivial `2^a` ceiling into `2^a · e^{−S}` where `S = ∑ δ_k`
  is the **total coherence-deficit budget** spent over the `a = log₂ n` levels.
* `prize_forces_linear_deficit_budget` — the **consequence**: if the telescoped value is to be pushed
  to a target `T ≤ 2^a · e^{−S} · M 0` strictly below `2^a · M 0` (i.e. `M 0 > 0`, `0 < T`), then
  `S ≥ log(2^a · M 0 / T)`.  Specialized to the prize target `T = C·√(2^a · a)` (BGK shape) this
  reads `S ≥ (a/2)·log 2 − ½·log a − log(C/M 0)`: the deficit budget the descent must spend grows
  **linearly in `a`** — a *sustained* `Ω(1)` coherence deficit at every level, with per-level average
  → `(log 2)/2 ≈ 0.347`.  (Numerically pinned in `/tmp/dil_budget.py`: required per-level avg
  0.217, 0.260, 0.292, 0.314 at `a = 8, 16, 32, 64`, ↗ `(log2)/2`.)

It does **NOT** prove that budget is achievable.  It uses **no** Gauss-period cancellation, **no**
moment, **no** completion, **no** anti-concentration estimate — only product-monotonicity, the
elementary `1 − x ≤ e^{−x}`, and `log`/`exp` bookkeeping.  This is a Lane-3 **constraint lemma**: it
prices the dilation route's exact budget, it does not pay it.  `M(μ_n) ≤ C·√(n·log(p/n))` stays
exactly as OPEN as before.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVDilationDeficitBudget

open scoped BigOperators
open Real Finset

/-- **Variable per-level dilation telescope.**  If a nonnegative level-indexed sequence `M` satisfies
the variable per-level bound `M (k+1) ≤ (2 − 2·δ k)·M k` for every level `k`, then after `a` levels
`M a ≤ (∏_{k<a} (2 − 2·δ k)) · M 0`.  This is the variable-factor generalization of
`_DoorIVDilationDescentTelescope.telescope_per_level_factor` (which fixes a single `c`), driven by the
per-level coherence-deficit weld `c_k ≤ 2 − 2·δ_k`. -/
theorem telescope_variable_factor (M : ℕ → ℝ) (δ : ℕ → ℝ)
    (_hδ0 : ∀ k, 0 ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1) (_hM : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ (2 - 2 * δ k) * M k) (a : ℕ) :
    M a ≤ (∏ k ∈ Finset.range a, (2 - 2 * δ k)) * M 0 := by
  induction a with
  | zero => simp
  | succ n ih =>
    have hfac_nonneg : (0 : ℝ) ≤ 2 - 2 * δ n := by
      have := hδ1 n; linarith
    calc M (n + 1) ≤ (2 - 2 * δ n) * M n := hstep n
      _ ≤ (2 - 2 * δ n) * ((∏ k ∈ Finset.range n, (2 - 2 * δ k)) * M 0) :=
          mul_le_mul_of_nonneg_left ih hfac_nonneg
      _ = (∏ k ∈ Finset.range (n + 1), (2 - 2 * δ k)) * M 0 := by
          rw [Finset.prod_range_succ]; ring

/-- **Algebraic split.**  `∏_{k<a} (2 − 2·δ k) = 2^a · ∏_{k<a} (1 − δ k)`.  Factors the trivial
doubling `2^a` out of the per-level deficit product, exposing the pure deficit factor `∏(1 − δ_k)`. -/
theorem prod_two_sub_two_deficit_eq (δ : ℕ → ℝ) (a : ℕ) :
    (∏ k ∈ Finset.range a, (2 - 2 * δ k))
      = 2 ^ a * ∏ k ∈ Finset.range a, (1 - δ k) := by
  have h2 : (2 : ℝ) ^ a = ∏ _k ∈ Finset.range a, (2 : ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h2, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _; ring

/-- **Multiplicative → additive (the engine).**  With each `δ k ≤ 1`, the deficit product is bounded by
the exponential of the *negated total*: `∏_{k<a} (1 − δ k) ≤ exp(−∑_{k<a} δ k)`.  Proof: pointwise
`1 − δ ≤ e^{−δ}` (`Real.add_one_le_exp`), product monotonicity (each factor `1 − δ_k ≥ 0`), then
`Real.exp_sum`. -/
theorem prod_one_sub_le_exp_neg_sum (δ : ℕ → ℝ) (hδ1 : ∀ k, δ k ≤ 1) (a : ℕ) :
    (∏ k ∈ Finset.range a, (1 - δ k)) ≤ Real.exp (-(∑ k ∈ Finset.range a, δ k)) := by
  have hptwise : ∀ k ∈ Finset.range a, (1 - δ k) ≤ Real.exp (-(δ k)) := by
    intro k _
    have := Real.add_one_le_exp (-(δ k))
    linarith
  have hnn : ∀ k ∈ Finset.range a, (0 : ℝ) ≤ 1 - δ k := by
    intro k _; have := hδ1 k; linarith
  calc (∏ k ∈ Finset.range a, (1 - δ k))
      ≤ ∏ k ∈ Finset.range a, Real.exp (-(δ k)) :=
        Finset.prod_le_prod hnn hptwise
    _ = Real.exp (∑ k ∈ Finset.range a, -(δ k)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ k ∈ Finset.range a, δ k)) := by rw [Finset.sum_neg_distrib]

/-- **The headline deficit-budget bound.**  Welding the variable telescope with the algebraic split and
the exp engine: the dilation descent's worst period after `a` levels is at most
`2^a · exp(−S) · M 0`, where `S = ∑_{k<a} δ_k` is the **total coherence-deficit budget** spent.

The trivial doubling ceiling is `2^a · M 0`; this theorem shows the descent can only improve it by the
factor `exp(−S)`.  To beat the dimension `2^a = n` toward the prize you must SPEND a budget `S`. -/
theorem telescope_deficit_budget (M : ℕ → ℝ) (δ : ℕ → ℝ)
    (hδ0 : ∀ k, 0 ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1) (hM : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ (2 - 2 * δ k) * M k) (a : ℕ) :
    M a ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M 0 := by
  have h1 : M a ≤ (∏ k ∈ Finset.range a, (2 - 2 * δ k)) * M 0 :=
    telescope_variable_factor M δ hδ0 hδ1 hM hstep a
  have h2 : (∏ k ∈ Finset.range a, (2 - 2 * δ k))
      = 2 ^ a * ∏ k ∈ Finset.range a, (1 - δ k) := prod_two_sub_two_deficit_eq δ a
  have h3 : (∏ k ∈ Finset.range a, (1 - δ k))
      ≤ Real.exp (-(∑ k ∈ Finset.range a, δ k)) :=
    prod_one_sub_le_exp_neg_sum δ hδ1 a
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ a := by positivity
  have hM0 : 0 ≤ M 0 := hM 0
  -- chain: M a ≤ (∏...)·M0 = 2^a·(∏(1-δ))·M0 ≤ 2^a·exp(-S)·M0
  calc M a ≤ (∏ k ∈ Finset.range a, (2 - 2 * δ k)) * M 0 := h1
    _ = 2 ^ a * (∏ k ∈ Finset.range a, (1 - δ k)) * M 0 := by rw [h2]
    _ ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M 0 := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact mul_le_mul_of_nonneg_left h3 hpow_nonneg

/-- **Prize forces a deficit budget (log form).**  Suppose the deficit-budget bound is good enough to
*certify* a strictly positive target `T`, i.e. `2^a · exp(−S) · M 0 ≤ T` (with `M 0 > 0`).  Then the
budget must satisfy `S ≥ log(2^a · M 0 / T)`.

Specialized to the BGK-shaped prize target `T = C·√(2^a · a)` this gives
`S ≥ (a/2)·log 2 − ½·log a − log(C / M 0)`, which is **linear in `a`**: the dilation route can certify
the prize only by spending a coherence-deficit budget that grows with the number of levels — a
*sustained* `Ω(1)` per-level deficit (average `→ (log 2)/2`), precisely the arithmetic
anti-concentration input the door-(iv) wall is missing.  This is a Lane-3 constraint lemma; it prices
the route, it does not prove the budget exists. -/
theorem prize_forces_linear_deficit_budget (M : ℕ → ℝ) (a : ℕ) (S T : ℝ)
    (hM0 : 0 < M 0) (_hT : 0 < T)
    (hbound : 2 ^ a * Real.exp (-S) * M 0 ≤ T) :
    S ≥ Real.log (2 ^ a * M 0 / T) := by
  -- From 2^a·e^{-S}·M0 ≤ T and T>0:  e^{-S} ≤ T/(2^a·M0), so -S ≤ log(T/(2^a M0)),
  -- i.e. S ≥ -log(T/(2^a M0)) = log(2^a M0 / T).
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hden_pos : (0 : ℝ) < 2 ^ a * M 0 := mul_pos hpow_pos hM0
  -- rearrange hbound to e^{-S} ≤ T / (2^a M0)
  have hexp_le : Real.exp (-S) ≤ T / (2 ^ a * M 0) := by
    rw [le_div_iff₀ hden_pos]
    -- goal: exp(-S) * (2^a * M0) ≤ T; hbound: 2^a * exp(-S) * M0 ≤ T
    calc Real.exp (-S) * (2 ^ a * M 0) = 2 ^ a * Real.exp (-S) * M 0 := by ring
      _ ≤ T := hbound
  -- take log (both sides positive)
  have hexp_pos : (0 : ℝ) < Real.exp (-S) := Real.exp_pos _
  have hlog_le : -S ≤ Real.log (T / (2 ^ a * M 0)) := by
    have := Real.log_le_log hexp_pos hexp_le
    rwa [Real.log_exp] at this
  -- log(T/(2^a M0)) = -log(2^a M0 / T)
  have hflip : Real.log (T / (2 ^ a * M 0)) = -Real.log (2 ^ a * M 0 / T) := by
    rw [← Real.log_inv]
    congr 1
    rw [inv_div]
  rw [hflip] at hlog_le
  linarith

end ArkLib.ProximityGap.Frontier.DoorIVDilationDeficitBudget
