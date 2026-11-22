/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Variance of the residual populations of an odd split pencil

After seven congruence classes are prescribed, each fiber has nine remaining
populations. Summing the lower displacement bound over the rotating group
bounds their total variance. An independent unit comparison bounds it below.
-/

set_option autoImplicit false

open Finset
namespace ArkLib.ProximityGap.Frontier.SplitPencilBlockVariance

/-- In nine equal blocks, total movement is determined by mass and variance. -/
theorem nine_block_identity (q M : ℚ) (t : Fin 9 → ℚ) (mass : ∑ j, t j = M) :
    (∑ j, (t j - M / 9) ^ 2) + (∑ j, t j * (q - t j)) = q * M - M ^ 2 / 9 := by
  rw [← sum_add_distrib]
  have h (j : Fin 9) :
      (t j - M / 9) ^ 2 + t j * (q - t j) = (q - 2 * M / 9) * t j + M ^ 2 / 81 := by
    ring
  simp_rw [h]
  rw [sum_add_distrib, ← mul_sum, mass]
  simp
  ring

/-- The aggregate displacement bound leaves only linear variance in the 3,2,2 case. -/
theorem three_two_two_upper (q V D : ℚ)
    (hrot : (q - 1) * (4 * q + 1) ≤ D)
    (hvar : V + D = q * (5 * q - 3) - ((q - 1) ^ 2 + 2 * (2 * q - 1) ^ 2) / 9) :
    9 * V ≤ 10 * q + 6 := by
  nlinarith

/-- The 3,3,1 distribution already spends more than the displacement budget. -/
theorem three_three_one_impossible (q V D : ℚ) (hq : 8 ≤ q) (hV : 0 ≤ V)
    (hrot : (q - 1) * (4 * q + 1) ≤ D)
    (hvar : V + D = q * (5 * q - 3) - (2 * (q - 1) ^ 2 + (3 * q - 1) ^ 2) / 9) :
    False := by
  nlinarith [sq_nonneg (q - 8)]

/-- A signed comparison of two rows controls its mismatch by the sum of both variances. -/
theorem comparison_bound (q O : ℚ) (h b c : Fin 9 → ℚ)
    (hgap : q * O / 9 = ∑ j, h j * (b j - c j)) :
    (q * O / 9) ^ 2 ≤ (∑ j, (h j) ^ 2) * (2 * ∑ j, ((b j) ^ 2 + (c j) ^ 2)) := by
  rw [hgap]
  refine (sum_mul_sq_le_sq_mul_sq univ h (fun j => b j - c j)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun _ _ => sq_nonneg _)
  rw [mul_sum]
  exact sum_le_sum fun j _ => by nlinarith [sq_nonneg (b j + c j)]

/-- The certified layout gap contradicts the rotation bound at every dyadic
block size at least sixteen. -/
theorem three_two_two_impossible (q V : ℚ) (hq : 16 ≤ q) (hrot : 9 * V ≤ 10 * q + 6)
    (hcomparison : 8 * q ^ 2 ≤ 99 * V) : False := by
  nlinarith [sq_nonneg (q - 16)]

end ArkLib.ProximityGap.Frontier.SplitPencilBlockVariance
