/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# G116: exact prefix summation for the effective HBK energy lane

The published proof of Heath--Brown--Konyagin Lemma 3 orders the nonzero intersection
fibers and controls every initial segment.  Its dyadic summation discards a substantial
constant.  The exact Abel identity below is the lossless replacement:

`sum a_i^2 = sum S_i (a_i-a_{i+1}) + S_N a_N`,

where `S_i = sum_{j <= i} a_j`.  For a decreasing nonnegative sequence, every coefficient
`a_i-a_{i+1}` is nonnegative, so an effective prefix estimate may be substituted termwise.
This isolates the genuinely analytic task (an explicit Stepanov prefix coefficient) from the
constant-preserving energy consumer.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G116HBKPrefixEnergySummation

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Lossless finite Abel summation for squares, with an explicit terminal term. -/
theorem sum_sq_eq_sum_prefix_mul_drop_add_terminal
    (a : ℕ → R) (N : ℕ) :
    ∑ i ∈ Finset.range N, a i ^ 2 =
      (∑ i ∈ Finset.range N,
        (∑ j ∈ Finset.range (i + 1), a j) * (a i - a (i + 1))) +
      (∑ j ∈ Finset.range N, a j) * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      ring

/-- Boundary-zero form used after padding a finite fiber list by zero. -/
theorem sum_sq_eq_sum_prefix_mul_drop
    (a : ℕ → R) (N : ℕ) (hN : a N = 0) :
    ∑ i ∈ Finset.range N, a i ^ 2 =
      ∑ i ∈ Finset.range N,
        (∑ j ∈ Finset.range (i + 1), a j) * (a i - a (i + 1)) := by
  rw [sum_sq_eq_sum_prefix_mul_drop_add_terminal, hN, mul_zero, add_zero]

section Ordered

/-- A decreasing, zero-padded sequence consumes any pointwise prefix majorant without a
dyadic loss.  This is the exact interface needed by an effective version of HBK Lemma 5. -/
theorem sum_sq_le_sum_majorant_mul_drop
    (a B : ℕ → ℝ) (N : ℕ) (hN : a N = 0)
    (hdrop : ∀ i < N, 0 ≤ a i - a (i + 1))
    (hprefix : ∀ i < N, (∑ j ∈ Finset.range (i + 1), a j) ≤ B i) :
    ∑ i ∈ Finset.range N, a i ^ 2 ≤
      ∑ i ∈ Finset.range N, B i * (a i - a (i + 1)) := by
  rw [sum_sq_eq_sum_prefix_mul_drop a N hN]
  apply Finset.sum_le_sum
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (hprefix i hiN) (hdrop i hiN)

end Ordered

end ArkLib.ProximityGap.Frontier.G116HBKPrefixEnergySummation

#print axioms
  ArkLib.ProximityGap.Frontier.G116HBKPrefixEnergySummation.sum_sq_eq_sum_prefix_mul_drop_add_terminal
#print axioms
  ArkLib.ProximityGap.Frontier.G116HBKPrefixEnergySummation.sum_sq_eq_sum_prefix_mul_drop
#print axioms
  ArkLib.ProximityGap.Frontier.G116HBKPrefixEnergySummation.sum_sq_le_sum_majorant_mul_drop
