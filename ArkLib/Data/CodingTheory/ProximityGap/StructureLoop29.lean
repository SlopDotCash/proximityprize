/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Loop 29 — additive fold factors: only the sum matters

Loop 27 showed that a uniform polynomial additive cost per fold is absorbed by one extra domain
power. This file records the variable-cost version. If the fold recurrence is additive,

    T(j+1) ≤ T(j) + b_j,

then after `m` folds the total contribution is exactly controlled by the sum

    T(m) ≤ T(0) + ∑_{j<m} b_j.

So an additive disproof cannot be based on one uneven or large-looking round. It must make the
**cumulative sum** of additive fold costs beat every polynomial in the smooth-domain size `2^m`.
If that sum is polynomially bounded, the prize numerator absorbs it.

Sorry-free and axiom-clean. See `DISPROOF_LOG.md` (Loop29).
-/

namespace ArkLib.ProximityGap.StructureLoop29

open scoped BigOperators

/-- **Variable additive fold recursion telescopes to the sum of additive costs.** The total additive
blowup after `m` folds is controlled by `∑_{j<m} b_j`; individual spikes matter only through this
cumulative sum. -/
theorem variable_additive_recursion_telescopes
    (T b : ℕ → ℝ) (hstep : ∀ j, T (j + 1) ≤ T j + b j) :
    ∀ m, T m ≤ T 0 + ∑ j ∈ Finset.range m, b j := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      calc
        T (n + 1) ≤ T n + b n := hstep n
        _ ≤ (T 0 + ∑ j ∈ Finset.range n, b j) + b n := by linarith
        _ = T 0 + ∑ j ∈ Finset.range (n + 1), b j := by
          rw [Finset.sum_range_succ]
          ring

/-- **Polynomially bounded additive sum is prize-safe.** If the cumulative additive fold cost is
bounded by a degree-`c` polynomial in the domain size `2^m`, then the whole additive tower is bounded
by the base plus that polynomial. A genuine additive disproof must therefore force the cumulative
sum, not merely one fold, to be super-polynomial. -/
theorem variable_additive_polynomial_of_sum_bound
    (T b : ℕ → ℝ) {B₀ : ℝ} {c m : ℕ}
    (hstep : ∀ j, T (j + 1) ≤ T j + b j) (hbase : T 0 ≤ B₀)
    (hsum : (∑ j ∈ Finset.range m, b j) ≤ ((2 : ℝ) ^ m) ^ c) :
    T m ≤ B₀ + ((2 : ℝ) ^ m) ^ c := by
  have htel := variable_additive_recursion_telescopes T b hstep m
  linarith

end ArkLib.ProximityGap.StructureLoop29

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop29.variable_additive_recursion_telescopes
#print axioms ArkLib.ProximityGap.StructureLoop29.variable_additive_polynomial_of_sum_bound
