/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Loop 27 — polynomial additive fold costs are also absorbed

The fold-tower disproof tries to accumulate per-round list growth across the `m = log₂ N` smooth
domain levels. This file records a self-refutation of the additive version: even if every fold
contributes a polynomial amount in the top domain size `N = 2^m`, summing over all `m` folds is still
polynomial. The logarithmic depth is absorbed by one extra domain power:

    m · (2^m)^c ≤ (2^m)^(c+1).

So an additive per-fold disproof cannot merely exhibit polynomially many new close codewords per
round. It must force a super-polynomial additive contribution, or else show genuinely multiplicative
branching whose cumulative product is super-polynomial. See `DISPROOF_LOG.md` (Loop27).
-/

namespace ArkLib.ProximityGap.StructureLoop27

/-- **The fold-depth logarithm is absorbed by one domain power.** Since `m ≤ 2^m`, summing a
degree-`c` polynomial contribution over the `m` folds is bounded by a degree-`c+1` polynomial in the
domain size `2^m`. -/
theorem fold_depth_mul_domain_pow_le_next_pow (c m : ℕ) :
    (m : ℝ) * (((2 : ℝ) ^ m) ^ c) ≤ ((2 : ℝ) ^ m) ^ (c + 1) := by
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    exact_mod_cast this.le
  have hnonneg : 0 ≤ (((2 : ℝ) ^ m) ^ c) := by positivity
  calc
    (m : ℝ) * (((2 : ℝ) ^ m) ^ c) ≤
        ((2 : ℝ) ^ m) * (((2 : ℝ) ^ m) ^ c) :=
      mul_le_mul_of_nonneg_right hm hnonneg
    _ = ((2 : ℝ) ^ m) ^ (c + 1) := by
      rw [pow_succ]
      ring

/-- **Polynomial additive per-fold cost is prize-safe.** If every fold adds at most a degree-`c`
polynomial in the top domain size `2^m`, then after all `m` folds the list is bounded by the base
plus a degree-`c+1` polynomial. Thus a polynomial additive fold cost cannot be the fixed-gap
super-polynomial lower bound required by the disproof route. -/
theorem additive_polynomial_step_le_next_pow
    (T : ℕ → ℝ) {B₀ C : ℝ} {c m : ℕ} (hC : 0 ≤ C)
    (hstep : ∀ j, T (j + 1) ≤ T j + C * (((2 : ℝ) ^ m) ^ c)) (hbase : T 0 ≤ B₀) :
    T m ≤ B₀ + C * (((2 : ℝ) ^ m) ^ (c + 1)) := by
  let b : ℝ := C * (((2 : ℝ) ^ m) ^ c)
  have hlin_all : ∀ k : ℕ, T k ≤ T 0 + (k : ℝ) * b := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        calc
          T (n + 1) ≤ T n + b := hstep n
          _ ≤ (T 0 + (n : ℝ) * b) + b := by linarith
          _ = T 0 + (n + 1 : ℕ) * b := by push_cast; ring
  have hlin : T m ≤ T 0 + (m : ℝ) * b := hlin_all m
  have hdepth : (m : ℝ) * b ≤ C * (((2 : ℝ) ^ m) ^ (c + 1)) := by
    dsimp [b]
    calc
      (m : ℝ) * (C * (((2 : ℝ) ^ m) ^ c)) =
          C * ((m : ℝ) * (((2 : ℝ) ^ m) ^ c)) := by ring
      _ ≤ C * (((2 : ℝ) ^ m) ^ (c + 1)) :=
        mul_le_mul_of_nonneg_left (fold_depth_mul_domain_pow_le_next_pow c m) hC
  linarith

end ArkLib.ProximityGap.StructureLoop27

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop27.fold_depth_mul_domain_pow_le_next_pow
#print axioms ArkLib.ProximityGap.StructureLoop27.additive_polynomial_step_le_next_pow
