/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# The C1 dyadic-tower variance recursion ⟹ sub-trivial sup-norm (#407)

Lead C1: the parallelogram (`DyadicTowerRecursion.period_parallelogram`) gives, for the dyadic period
variance `V_μ = max_{b≠0}‖η_b^{(μ)}‖²`, the recursion `V_μ ≤ 4·ratio_μ·V_{μ-1}` where `ratio_μ ∈ (0,1]`
is the per-level deficit (the worst level-μ frequency's two sub-periods are sub-maximal). MEASURED
`ratio_μ ≈ 0.7`, so `V_μ ≤ 2.8·V_{μ-1}` ⟹ `M ≤ n^{0.74..0.88}` — **below the analytic SOTA di Benedetto
`n^{0.989}`** (the gap to prize `√n` is the residual: the deficit plateaus at ~0.7, not 0.5).

This file formalizes the recursion's consequence, conditional on a uniform deficit bound:

> **`variance_geom_bound`** — if `V_{k+1} ≤ A·V_k` for all `k` (with `0 ≤ A`, `V ≥ 0`), then
> `V_μ ≤ A^μ·V_0`.
> **`supNorm_le_of_deficit`** — with `A = 4c`, `V_μ = M_μ²`, `n = 2^μ`: `M_μ ≤ (4c)^{μ/2}·√(V_0)`,
> i.e. `M ≤ n^{log₂(4c)/2}·√(V_0)`. For `c < 1/2` this beats `√n`; the measured `c≈0.7` gives the
> sub-SOTA exponent `log₂(2.8)/2 ≈ 0.74`.

The single open input is the uniform per-level deficit `ratio_μ ≤ c < 1` (equiv: the worst level-μ
frequency `b` does not make BOTH `‖η_b^{(μ-1)}‖` and `‖η_{bω}^{(μ-1)}‖` maximal — the worst-frequency
sets interleave under the `ω`-shift). That inequality is the C1 "deficit brick", still open.

Issue #407.
-/

namespace ArkLib.ProximityGap.C1ConditionalBound

/-- **Geometric tower recursion.** A nonnegative sequence with `V_{k+1} ≤ A·V_k` (`A ≥ 0`) satisfies
`V_μ ≤ A^μ·V_0`. This is the C1 tower variance recursion: `V_μ = max‖η^{(μ)}‖²`, `A = 4·(deficit)`. -/
theorem variance_geom_bound (V : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) (hV : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ A * V k) (μ : ℕ) : V μ ≤ A ^ μ * V 0 := by
  induction μ with
  | zero => simp
  | succ m ih =>
    calc V (m + 1) ≤ A * V m := hrec m
      _ ≤ A * (A ^ m * V 0) := by exact mul_le_mul_of_nonneg_left ih hA
      _ = A ^ (m + 1) * V 0 := by ring

/-- **C1 sup-norm bound, conditional on the deficit.** If the variance `V_k` satisfies the deficit
recursion `V_{k+1} ≤ 4c·V_k` (`0 ≤ c`), then `V_μ ≤ (4c)^μ·V_0`. Taking square roots, the sup-norm
`M_μ = √(V_μ)` obeys `M_μ ≤ (4c)^{μ/2}·√(V_0) = n^{log₂(4c)/2}·√(V_0)` with `n = 2^μ`; `c < 1/2` beats
`√n`. Conditional only on the open per-level deficit `ratio_μ ≤ c`. -/
theorem supNorm_le_of_deficit (V : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hV : ∀ k, 0 ≤ V k)
    (hrec : ∀ k, V (k + 1) ≤ (4 * c) * V k) (μ : ℕ) :
    Real.sqrt (V μ) ≤ (4 * c) ^ ((μ : ℝ) / 2) * Real.sqrt (V 0) := by
  have hgeom : V μ ≤ (4 * c) ^ μ * V 0 :=
    variance_geom_bound V (4 * c) (by positivity) hV hrec μ
  calc Real.sqrt (V μ)
      ≤ Real.sqrt ((4 * c) ^ μ * V 0) := Real.sqrt_le_sqrt hgeom
    _ = Real.sqrt ((4 * c) ^ μ) * Real.sqrt (V 0) := Real.sqrt_mul (by positivity) _
    _ = (4 * c) ^ ((μ : ℝ) / 2) * Real.sqrt (V 0) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (4 * c) μ, ← Real.rpow_mul (by positivity)]
        congr 1
        ring

end ArkLib.ProximityGap.C1ConditionalBound

#print axioms ArkLib.ProximityGap.C1ConditionalBound.variance_geom_bound
#print axioms ArkLib.ProximityGap.C1ConditionalBound.supNorm_le_of_deficit
