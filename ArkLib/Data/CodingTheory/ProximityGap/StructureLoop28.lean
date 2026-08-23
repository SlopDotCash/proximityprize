/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Loop 28 — variable fold factors: only the product matters

A multiplicative fold-tower disproof cannot rely on the existence of one large fold factor. If the
fold recurrence has variable factors

    T(j+1) ≤ a_j · T(j),

then telescoping gives

    T(m) ≤ (∏_{j<m} a_j) · T(0).

Therefore any variable-factor analysis whose total product is bounded by `(2^m)^c` is still
polynomial in the smooth-domain size and is absorbed by the prize numerator. A multiplicative
disproof must make the cumulative product beat every polynomial in `2^m`; isolated large folds, or
polynomially bounded products, do not suffice. See `DISPROOF_LOG.md` (Loop28).
-/

namespace ArkLib.ProximityGap.StructureLoop28

open scoped BigOperators

/-- **Variable-factor fold recursion telescopes to the product of factors.** With factors `a_j`, the
full multiplicative blowup is `∏_{j<m} a_j`. -/
theorem variable_fold_recursion_telescopes
    (T a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hstep : ∀ j, T (j + 1) ≤ a j * T j) :
    ∀ m, T m ≤ (∏ j ∈ Finset.range m, a j) * T 0 := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      calc
        T (n + 1) ≤ a n * T n := hstep n
        _ ≤ a n * ((∏ j ∈ Finset.range n, a j) * T 0) :=
          mul_le_mul_of_nonneg_left ih (ha n)
        _ = (∏ j ∈ Finset.range (n + 1), a j) * T 0 := by
          rw [Finset.prod_range_succ]
          ring

/-- **Polynomially bounded product is prize-safe.** If the cumulative variable fold product is at
most `(2^m)^c`, then the multiplicative tower contributes only a degree-`c` polynomial in the domain
size. Thus a multiplicative disproof needs a super-polynomial **product**, not merely one large
per-fold factor. -/
theorem variable_fold_polynomial_of_product_bound
    (T a : ℕ → ℝ) {c m : ℕ} (ha : ∀ j, 0 ≤ a j) (hT0 : 0 ≤ T 0)
    (hstep : ∀ j, T (j + 1) ≤ a j * T j)
    (hprod : (∏ j ∈ Finset.range m, a j) ≤ ((2 : ℝ) ^ m) ^ c) :
    T m ≤ ((2 : ℝ) ^ m) ^ c * T 0 := by
  refine le_trans (variable_fold_recursion_telescopes T a ha hstep m) ?_
  exact mul_le_mul_of_nonneg_right hprod hT0

end ArkLib.ProximityGap.StructureLoop28

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop28.variable_fold_recursion_telescopes
#print axioms ArkLib.ProximityGap.StructureLoop28.variable_fold_polynomial_of_product_bound
