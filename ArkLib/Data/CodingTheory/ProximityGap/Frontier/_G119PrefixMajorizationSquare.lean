/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# G119: sharp prefix majorization for squared mass

HBK orders the intersection fibers decreasingly and bounds every prefix.  The correct lossless
consumer is the finite Hardy--Littlewood--Pólya principle: if decreasing sequences `a,c` have equal
total mass and every prefix of `a` is bounded by the corresponding prefix of `c`, then

`sum a_i^2 ≤ sum c_i^2`.

This file proves the result directly from two finite Abel identities.  No dyadic decomposition,
geometric-series constant, measure theory, or asymptotic notation is used. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G119PrefixMajorizationSquare

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Bilinear finite Abel summation with an explicit terminal term. -/
theorem sum_mul_eq_sum_prefix_mul_drop_add_terminal
    (x y : ℕ → R) (N : ℕ) :
    ∑ i ∈ Finset.range N, x i * y i =
      (∑ i ∈ Finset.range N,
        (∑ j ∈ Finset.range (i + 1), x j) * (y i - y (i + 1))) +
      (∑ j ∈ Finset.range N, x j) * y N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      ring

/-- Zero-boundary form of bilinear Abel summation. -/
theorem sum_mul_eq_sum_prefix_mul_drop
    (x y : ℕ → R) (N : ℕ) (hyN : y N = 0) :
    ∑ i ∈ Finset.range N, x i * y i =
      ∑ i ∈ Finset.range N,
        (∑ j ∈ Finset.range (i + 1), x j) * (y i - y (i + 1)) := by
  rw [sum_mul_eq_sum_prefix_mul_drop_add_terminal, hyN, mul_zero, add_zero]

/-- Prefix domination against a decreasing test sequence. -/
theorem sum_mul_le_sum_mul_of_prefix_le
    (a c : ℕ → ℝ) (N : ℕ) (hcN : c N = 0)
    (hcdrop : ∀ i < N, 0 ≤ c i - c (i + 1))
    (hprefix : ∀ i < N,
      (∑ j ∈ Finset.range (i + 1), a j) ≤
        ∑ j ∈ Finset.range (i + 1), c j) :
    ∑ i ∈ Finset.range N, a i * c i ≤
      ∑ i ∈ Finset.range N, c i * c i := by
  rw [sum_mul_eq_sum_prefix_mul_drop a c N hcN,
    sum_mul_eq_sum_prefix_mul_drop c c N hcN]
  apply Finset.sum_le_sum
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_right (hprefix i hiN) (hcdrop i hiN)

/-- **Sharp squared-mass majorization.** A decreasing sequence below all prefixes of a decreasing
comparison sequence has no larger `L²` mass.  Equality of total mass is encoded by padding both
sequences with zero and including the final prefix among `hprefix`; no positivity assumption on the
individual entries is needed beyond the two decreasing hypotheses used by Abel summation. -/
theorem sum_sq_le_sum_sq_of_prefix_le
    (a c : ℕ → ℝ) (N : ℕ) (haN : a N = 0) (hcN : c N = 0)
    (hadrop : ∀ i < N, 0 ≤ a i - a (i + 1))
    (hcdrop : ∀ i < N, 0 ≤ c i - c (i + 1))
    (hprefix : ∀ i < N,
      (∑ j ∈ Finset.range (i + 1), a j) ≤
        ∑ j ∈ Finset.range (i + 1), c j) :
    ∑ i ∈ Finset.range N, a i ^ 2 ≤
      ∑ i ∈ Finset.range N, c i ^ 2 := by
  rw [show (∑ i ∈ Finset.range N, a i ^ 2) =
      ∑ i ∈ Finset.range N, a i * a i by
        apply Finset.sum_congr rfl
        intro i _
        ring]
  rw [sum_mul_eq_sum_prefix_mul_drop a a N haN]
  calc
    (∑ i ∈ Finset.range N,
        (∑ j ∈ Finset.range (i + 1), a j) * (a i - a (i + 1))) ≤
        ∑ i ∈ Finset.range N,
          (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_right (hprefix i hiN) (hadrop i hiN)
    _ = ∑ i ∈ Finset.range N, c i * a i := by
      symm
      exact sum_mul_eq_sum_prefix_mul_drop c a N haN
    _ = ∑ i ∈ Finset.range N, a i * c i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ Finset.range N, c i * c i :=
      sum_mul_le_sum_mul_of_prefix_le a c N hcN hcdrop hprefix
    _ = ∑ i ∈ Finset.range N, c i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring

end ArkLib.ProximityGap.Frontier.G119PrefixMajorizationSquare

#print axioms
  ArkLib.ProximityGap.Frontier.G119PrefixMajorizationSquare.sum_mul_eq_sum_prefix_mul_drop_add_terminal
#print axioms
  ArkLib.ProximityGap.Frontier.G119PrefixMajorizationSquare.sum_mul_le_sum_mul_of_prefix_le
#print axioms
  ArkLib.ProximityGap.Frontier.G119PrefixMajorizationSquare.sum_sq_le_sum_sq_of_prefix_le
