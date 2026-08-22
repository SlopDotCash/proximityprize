/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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
bound does NOT refute the prize.**  Writing `M_k` for the worst-case modulus at level `k`, the
near-Ramanujan / prize scale is `M_μ ≤ √(2^μ)·M_0 = √n · M_0` (up to the `polylog` we suppress),
which telescopes as

  `M_μ / M_0 = ∏_{k<μ} (M_k.succ / M_k)`.

So the prize asks only that the **geometric mean** of the per-step ratios be `≤ √2` — equivalently
that the **Lyapunov exponent** `lim (1/μ) Σ log(M_k.succ/M_k) ≤ ½ log 2`.  Individual ratios may
exceed `√2` as long as the *average* does not.  We prove:

* `M_le_of_uniform_perstep` — the uniform per-step bound is **sufficient** (it telescopes to the
  prize scale), and
* `uniform_not_necessary` — it is **not necessary**: an explicit two-step sequence with a ratio
  `> √2` at one step still meets the telescoped prize bound `M_2 ≤ (√2)^2 · M_0`.

The honest upshot: the open object is the **average/Lyapunov** bound on the butterfly ratios, which
is strictly weaker than the (refuted) uniform per-step bound.  `_Attack01`'s numerical refutation
prunes one inductive route but leaves the prize-relevant (geometric-mean) statement open — that
average bound is exactly the BGK/Paley wall, but it is *not* contradicted by the per-step data.

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

/-- **Uniform per-step `√2` is SUFFICIENT.** If every step contracts by `√2`, the worst-case
modulus reaches only the prize scale `(√2)^μ · M_0 = √(2^μ) · M_0 = √n · M_0`. -/
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
contraction (as the numerics do) does not refute the prize-scale (geometric-mean) bound. -/
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
    linarith

end ArkLib.ProximityGap.Attack01bLyapunov

#print axioms ArkLib.ProximityGap.Attack01bLyapunov.M_eq_mul_prod_ratio
#print axioms ArkLib.ProximityGap.Attack01bLyapunov.M_le_of_uniform_perstep
#print axioms ArkLib.ProximityGap.Attack01bLyapunov.uniform_not_necessary
