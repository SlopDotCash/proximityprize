/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Integer enclosures for the joint locator ellipsoid

Rounding every Gram–Schmidt coefficient with absolute error at most one
widens a coordinate's interval by the sum of the absolute values of the
already fixed coefficients. Rounding the positive weights down then gives
a necessary inequality for every vector in the original ellipsoid.
-/

namespace ProximityGap.JointLocatorRounding

/-- A row of the rounded triangular form has this total error. -/
theorem affine_error {I : Type*} (s : Finset I) (z a b : I → ℝ) (base : ℝ)
    (hab : ∀ i ∈ s, |a i - b i| ≤ 1) :
    |(base + ∑ i ∈ s, z i * a i) - (base + ∑ i ∈ s, z i * b i)| ≤ ∑ i ∈ s, |z i| := by
  have he : (base + ∑ i ∈ s, z i * a i) - (base + ∑ i ∈ s, z i * b i) =
      ∑ i ∈ s, z i * (a i - b i) := by simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi ↦ by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hab i hi) (abs_nonneg (z i))))

/-- Every branch of a true ellipsoid point passes the rounded squared-distance test. -/
theorem rounded_energy {I : Type*} (s : Finset I) (approx exact err lo hi : I → ℝ)
    (herror : ∀ i ∈ s, |approx i - exact i| ≤ err i)
    (hlo : ∀ i ∈ s, 0 ≤ lo i) (hweights : ∀ i ∈ s, lo i ≤ hi i) :
    ∑ i ∈ s, lo i * max 0 (|approx i| - err i)^2 ≤
      ∑ i ∈ s, hi i * (exact i)^2 := by
  apply Finset.sum_le_sum
  intro i h
  have ht : |approx i| ≤ err i + |exact i| := calc
    |approx i| = |(approx i - exact i) + exact i| := by rw [sub_add_cancel]
    _ ≤ |approx i - exact i| + |exact i| := abs_add_le _ _
    _ ≤ err i + |exact i| := add_le_add (herror i h) le_rfl
  have hd : max 0 (|approx i| - err i) ≤ |exact i| :=
    max_le (abs_nonneg _) (by linarith)
  have hp : max 0 (|approx i| - err i)^2 ≤ (exact i)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (le_max_left _ _) hd 2
  exact (mul_le_mul_of_nonneg_left hp (hlo i h)).trans
    (mul_le_mul_of_nonneg_right (hweights i h) (sq_nonneg _))

#print axioms affine_error
#print axioms rounded_energy

end ProximityGap.JointLocatorRounding
