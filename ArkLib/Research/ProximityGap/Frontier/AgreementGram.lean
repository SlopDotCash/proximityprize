/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Finite Gram matrix estimates for agreement vectors -/

namespace ProximityGap.AgreementGram

variable {ι α : Type*}

/-- The sum of the entries of a real Gram matrix is the squared norm of the
sum of the vectors. -/
theorem sum_dot_nonneg (S : Finset ι) (X : Finset α) (v : ι → α → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, ∑ x ∈ X, v i x * v j x := by
  have h : ∑ i ∈ S, ∑ j ∈ S, ∑ x ∈ X, v i x * v j x =
      ∑ x ∈ X, (∑ i ∈ S, v i x) ^ 2 := by
    simp only [sq, Finset.sum_mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [h]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The two Gram matrices of a rectangular matrix have equal sums of squared entries. -/
theorem sum_sq_dot_comm (S : Finset ι) (X : Finset α) (v : ι → α → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, (∑ x ∈ X, v i x * v j x) ^ 2 =
      ∑ x ∈ X, ∑ y ∈ X, (∑ i ∈ S, v i x * v i y) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  conv_lhs =>
    enter [2, i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The finite real Welch bound. The vectors on the selected index set have a
common squared norm `V` and use at most `X.card` coordinates. -/
theorem sq_card_mul_sq_norm_le (S : Finset ι) (X : Finset α) (v : ι → α → ℝ) (V : ℝ)
    (hnorm : ∀ i ∈ S, ∑ x ∈ X, (v i x) ^ 2 = V) :
    (S.card : ℝ) ^ 2 * V ^ 2 ≤
      (X.card : ℝ) * ∑ i ∈ S, ∑ j ∈ S, (∑ x ∈ X, v i x * v j x) ^ 2 := by
  have trace : ∑ x ∈ X, ∑ i ∈ S, v i x * v i x = (S.card : ℝ) * V := by
    rw [Finset.sum_comm]
    simp only [← sq]
    rw [Finset.sum_congr rfl hnorm, Finset.sum_const, nsmul_eq_mul]
  have diagonal : ∑ x ∈ X, (∑ i ∈ S, v i x * v i x) ^ 2 ≤
      ∑ x ∈ X, ∑ y ∈ X, (∑ i ∈ S, v i x * v i y) ^ 2 := by
    apply Finset.sum_le_sum
    intro x hx
    exact Finset.single_le_sum (fun y _ => sq_nonneg (∑ i ∈ S, v i x * v i y)) hx
  rw [← mul_pow, ← trace, sum_sq_dot_comm]
  exact (sq_sum_le_card_mul_sum_sq (s := X) (f := fun x => ∑ i ∈ S, v i x * v i x)).trans
    (mul_le_mul_of_nonneg_left diagonal (Nat.cast_nonneg _))

#print axioms sum_dot_nonneg
#print axioms sum_sq_dot_comm
#print axioms sq_card_mul_sq_norm_le

end ProximityGap.AgreementGram
