/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Log-convexity of the Gauss-period moment ladder (#407)

The moment sequence `A_r = ∑_b a_b^r` (with `a_b = ‖η_b‖² ≥ 0`) is **log-convex** in `r`:

> **`sum_pow_sq_le_mul`** — for `0 ≤ a` and `r ≥ 1`, `(∑ a^r)² ≤ (∑ a^{r-1})·(∑ a^{r+1})`.

This is the Cauchy–Schwarz structure underlying the moment method: it makes `log A_r` convex, so the
optimal moment order is well-defined and the bound `M^{2r} ≤ A_r` tightens monotonically toward the
optimum `r ≈ log q`. (It is also why a single bad moment cannot be "interpolated away": the ladder is
rigid.) Char-free and unconditional.

Issue #407.
-/

open Finset

namespace ArkLib.ProximityGap.MomentLogConvex

variable {ι : Type*} [Fintype ι]

/-- **Moment log-convexity (Cauchy–Schwarz).** For a nonnegative function `a : ι → ℝ` and `r ≥ 1`,
`(∑ a^r)² ≤ (∑ a^{r-1})·(∑ a^{r+1})`. Hence `r ↦ log(∑ a^r)` is convex — the moment ladder is rigid. -/
theorem sum_pow_sq_le_mul (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (r : ℕ) (hr : 1 ≤ r) :
    (∑ i, a i ^ r) ^ 2 ≤ (∑ i, a i ^ (r - 1)) * (∑ i, a i ^ (r + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  -- Cauchy–Schwarz with `f = √(a^k)`, `g = √(a^{k+2})`: `f·g = a^{k+1}`, `f² = a^k`, `g² = a^{k+2}`.
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (a i ^ k)) (fun i => Real.sqrt (a i ^ (k + 2)))
  have hfg : ∀ i, Real.sqrt (a i ^ k) * Real.sqrt (a i ^ (k + 2)) = a i ^ (k + 1) := by
    intro i
    rw [← Real.sqrt_mul (pow_nonneg (ha i) k), ← pow_add,
        show k + (k + 2) = (k + 1) * 2 by ring, pow_mul, Real.sqrt_sq (pow_nonneg (ha i) (k + 1))]
  have hf2 : ∀ i, Real.sqrt (a i ^ k) ^ 2 = a i ^ k := fun i => Real.sq_sqrt (pow_nonneg (ha i) k)
  have hg2 : ∀ i, Real.sqrt (a i ^ (k + 2)) ^ 2 = a i ^ (k + 2) :=
    fun i => Real.sq_sqrt (pow_nonneg (ha i) (k + 2))
  simp only [hfg] at key
  simp only [hf2, hg2] at key
  simpa using key

end ArkLib.ProximityGap.MomentLogConvex

#print axioms ArkLib.ProximityGap.MomentLogConvex.sum_pow_sq_le_mul
