/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Attack #01b: the geometric-mean (Lyapunov) lever — the per-step refutation does NOT refute the prize

`_Attack01DyadicButterfly.lean` records the exact FFT butterfly recursion
`η_k(b) = η_{k-1}(b) + η_{k-1}(b·ζ_k)` and its named open obligation
`DyadicPerStepContraction`: the **uniform per-step** bound `‖η_k(b)‖ ≤ √2 · M_{k-1}` for *every* `b`
and *every* level `k`.  That predicate is **refuted numerically** (the per-step ratio
`M_k/M_{k-1}` oscillates in `[0.8, 2.0]`).

This file isolates a subtle but important correction: **the refutation of the uniform per-step
bound does NOT refute the prize.**  Writing `M_k` for the worst-case modulus at level `k` of one
fixed finite tower (fixed field, fixed top depth `μ`), the positive sequence telescopes exactly as

  `M_μ / M_0 = ∏_{k<μ} (M_k.succ / M_k)`   (`M_eq_mul_prod_ratio`).

The prize-scale estimate is a **finite-depth cumulative** bound: the product of the per-step ratios
up to the top depth must be at most `C · √(2^μ) · polylog` with a uniform constant `C`,
equivalently the cumulative log-ratio `Σ_{k<μ} log(M_k.succ/M_k) ≤ (μ/2)·log 2 + O(log μ)` (with
the logarithmic remainder in whatever polylog parameter the prize statement fixes). Individual
ratios may exceed `√2` as long as the *cumulative* product stays within budget.

This is **not** the same as a limiting Lyapunov exponent `lim (1/μ) Σ log(ratio) ≤ ½ log 2`. At
the critical value `½ log 2` the limit forgets the size of the subexponential remainder: e.g. the
positive sequence `M_μ = (√2)^μ · exp(√μ)` has limiting average log-ratio exactly `½ log 2`, yet
`M_μ / √(2^μ) = exp(√μ)` exceeds every fixed polylogarithmic factor in `2^μ`. (This shows only that
the two formulations are not equivalent; it does not claim that this sequence is a realized
period-max family.) A limiting statement would suffice only with a *strictly smaller* exponent and
explicit parameter comparisons. Also, an asymptotic sequence of growing-field towers is a
different object from the levels of one fixed-field finite tower; the telescope here concerns the
latter.

We prove:

* `M_eq_mul_prod_ratio` — the exact telescope;
* `M_le_of_cumulative` — the finite-depth cumulative product bound is what controls `M_μ`;
* `M_le_of_uniform_perstep` — the uniform per-step bound is **sufficient** (it telescopes to the
  scale `(√2)^μ · M_0`), and
* `uniform_not_necessary` — it is **not necessary**: an explicit two-step sequence with a ratio
  `> √2` at one step still meets the telescoped bound `M_2 ≤ (√2)^2 · M_0`.

The honest upshot: the open object is a **finite-depth cumulative** bound on the butterfly ratios
(with uniform constant and logarithmic remainder), which is strictly weaker than the (refuted)
uniform per-step bound.  `_Attack01`'s numerical refutation prunes one inductive route but leaves
the prize-relevant cumulative statement open — that bound is the BGK/Paley wall, and it is *not*
contradicted by the per-step data.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #464.
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.Attack01bLyapunov

/-- **Telescoping.** For a positive sequence `M`, the level-`μ` value is the level-`0` value times
the product of the per-step ratios. -/
theorem M_eq_mul_prod_ratio (M : ℕ → ℝ) (hpos : ∀ k, 0 < M k) (μ : ℕ) :
    M μ = M 0 * ∏ k ∈ Finset.range μ, (M (k + 1) / M k) := by
  induction μ with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ]
      calc
        M (m + 1) = M m * (M (m + 1) / M m) := by
          field_simp [ne_of_gt (hpos m)]
      _ = (M 0 * ∏ k ∈ Finset.range m, (M (k + 1) / M k)) *
            (M (m + 1) / M m) := by rw [ih]
      _ = M 0 * ((∏ k ∈ Finset.range m, (M (k + 1) / M k)) *
            (M (m + 1) / M m)) := by ring

/-- **Finite-depth cumulative bound.** If the product of the per-step ratios up to depth `μ` is at
most `B`, then `M μ ≤ B · M 0`. This is the form the prize-scale estimate takes, with
`B = C · (√2)^μ · polylog` for a uniform constant `C`; no per-step bound and no limiting exponent
is needed. -/
theorem M_le_of_cumulative (M : ℕ → ℝ) (hpos : ∀ k, 0 < M k) (μ : ℕ) (B : ℝ)
    (h : ∏ k ∈ Finset.range μ, (M (k + 1) / M k) ≤ B) :
    M μ ≤ B * M 0 := by
  rw [M_eq_mul_prod_ratio M hpos μ, mul_comm (M 0)]
  exact mul_le_mul_of_nonneg_right h (le_of_lt (hpos 0))

/-- **Uniform per-step `√2` is SUFFICIENT.** If every step grows by at most `√2`, the worst-case
modulus reaches only the scale `(√2)^μ · M_0 = √(2^μ) · M_0 = √n · M_0`. -/
theorem M_le_of_uniform_perstep (M : ℕ → ℝ) (hpos : ∀ k, 0 < M k) (μ : ℕ)
    (h : ∀ k < μ, M (k + 1) ≤ Real.sqrt 2 * M k) :
    M μ ≤ (Real.sqrt 2) ^ μ * M 0 := by
  induction μ with
  | zero => simp
  | succ m ih =>
    have hstep : M (m + 1) ≤ Real.sqrt 2 * M m := h m (Nat.lt_succ_self m)
    have ihm : M m ≤ (Real.sqrt 2) ^ m * M 0 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc M (m + 1) ≤ Real.sqrt 2 * M m := hstep
      _ ≤ Real.sqrt 2 * ((Real.sqrt 2) ^ m * M 0) := by
          exact mul_le_mul_of_nonneg_left ihm hs0
      _ = (Real.sqrt 2) ^ (m + 1) * M 0 := by ring

end ArkLib.ProximityGap.Attack01bLyapunov

namespace ArkLib.ProximityGap.Attack01bLyapunov

/-- **Uniform per-step `√2` is NOT NECESSARY.** Explicit two-step witness `M = (1, 2, 2)`: the
first ratio is `2 > √2` (so the uniform per-step bound *fails* at step 0), yet the telescoped
prize bound `M_2 ≤ (√2)^2 · M_0 = 2` *holds* with equality.  Hence refuting the uniform per-step
contraction (as the numerics do) does not refute the prize-scale (cumulative) bound. -/
theorem uniform_not_necessary :
    ∃ M : ℕ → ℝ, (∀ k, 0 < M k) ∧
      M 2 ≤ (Real.sqrt 2) ^ 2 * M 0 ∧            -- prize-scale telescoped bound HOLDS
      ¬ (M 1 ≤ Real.sqrt 2 * M 0) := by          -- uniform per-step bound FAILS at step 0
  refine ⟨fun k => if k = 0 then 1 else 2, ?_, ?_, ?_⟩
  · intro k; by_cases hk : k = 0 <;> simp [hk] <;> norm_num
  · -- M 2 = 2 ≤ (√2)^2 · 1 = 2
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [show (2 : ℕ) ≠ 0 from by norm_num, if_neg, show (0 : ℕ) = 0 from rfl, if_pos]
    rw [h2]; norm_num
  · -- M 1 = 2 > √2 · 1 = √2
    have hlt : Real.sqrt 2 < 2 := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 4)
      rwa [show Real.sqrt 4 = 2 from by
        rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]] at this
    simp only [show (1 : ℕ) ≠ 0 from by norm_num, if_neg, if_pos]
    norm_num

end ArkLib.ProximityGap.Attack01bLyapunov

#print axioms ArkLib.ProximityGap.Attack01bLyapunov.M_eq_mul_prod_ratio
#print axioms ArkLib.ProximityGap.Attack01bLyapunov.M_le_of_cumulative
#print axioms ArkLib.ProximityGap.Attack01bLyapunov.M_le_of_uniform_perstep
#print axioms ArkLib.ProximityGap.Attack01bLyapunov.uniform_not_necessary
