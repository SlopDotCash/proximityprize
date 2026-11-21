/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Fourier certificate for a prescribed interval of Paley differences

Truncating a difference kernel to the differences used in a rectangle allows its
short Fourier sums to bound every choice of weights on the two sets. The group
and the kernel here are arbitrary. The analytic application takes the kernel to
be a quadratic character on an interval and zero elsewhere.
-/

namespace ProximityGap.PaleyIntervalSpectrum

open Finset ZMod
open scoped ComplexConjugate

variable {p : ℕ} [NeZero p]

/-- Parseval's identity for the unnormalized discrete Fourier transform. -/
theorem dft_sum_sq (f : ZMod p → ℂ) :
    ∑ k, ‖dft f k‖ ^ 2 = p * ∑ x, ‖f x‖ ^ 2 := by
  have inv (x : ZMod p) : ∑ k, stdAddChar (k * x) * dft f k = (p : ℂ) * f x := by
    have h := congrFun (dft.symm_apply_apply f) x
    rw [invDFT_apply] at h
    simp only [smul_eq_mul] at h
    rw [← h, ← mul_assoc, mul_inv_cancel₀ (NeZero.ne (p : ℂ)), one_mul]
  have prod (z : ℂ) : conj z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have h : ∑ k, conj (dft f k) * dft f k = (p : ℂ) * ∑ x, conj (f x) * f x := by
    calc
      _ = ∑ k, ∑ x, conj (f x) * (stdAddChar (k * x) * dft f k) := by
        apply sum_congr rfl
        intro k _
        conv_lhs => arg 1; arg 2; rw [dft_apply]
        simp only [smul_eq_mul, map_sum, map_mul, ← AddChar.map_neg_eq_conj, neg_neg, sum_mul]
        apply sum_congr rfl
        intro x _
        rw [mul_comm x k]
        ring
      _ = _ := by
        rw [sum_comm, mul_sum]
        apply sum_congr rfl
        intro x _
        rw [← mul_sum, inv]
        ring
  simp only [prod] at h
  exact_mod_cast h

/-- The action of a difference kernel on a column weight. -/
noncomputable def applyKernel (K v : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  ∑ y, K (x - y) * v y

/-- Fourier diagonalization with the normalization used in the interval estimate. -/
theorem dft_applyKernel (K v : ZMod p → ℂ) (k : ZMod p) :
    dft (applyKernel K v) k = dft K k * dft v k := by
  simp only [dft_apply, smul_eq_mul, applyKernel, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply]
  rw [show -(x * k) = -((x - y) * k) + -(y * k) by ring, AddChar.map_add_eq_mul]
  ring

/-- A bound on every Fourier coefficient controls the action on every weight. -/
theorem applyKernel_sum_sq (K v : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ k, ‖dft K k‖ ≤ M) :
    ∑ x, ‖applyKernel K v x‖ ^ 2 ≤ M ^ 2 * ∑ y, ‖v y‖ ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply le_of_mul_le_mul_left (a := (p : ℝ)) _ hp
  rw [← dft_sum_sq, mul_left_comm, ← dft_sum_sq, mul_sum]
  apply sum_le_sum
  intro k _
  rw [dft_applyKernel, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM k) 2) (sq_nonneg _)

/-- For prescribed row and column supports, the kernel need only agree on their differences. -/
theorem rectangle_bound (K W u v : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ k, ‖dft K k‖ ≤ M)
    (hagree : ∀ x y, u x ≠ 0 → v y ≠ 0 → K (x - y) = W (x - y)) :
    ‖∑ x, ∑ y, u x * W (x - y) * v y‖ ^ 2 ≤
      M ^ 2 * (∑ x, ‖u x‖^2) * ∑ y, ‖v y‖^2 := by
  have heq : ∑ x, ∑ y, u x * W (x - y) * v y = ∑ x, u x * applyKernel K v x := by
    apply sum_congr rfl
    intro x _
    rw [applyKernel, mul_sum]
    apply sum_congr rfl
    intro y _
    by_cases hu : u x = 0
    · simp [hu]
    by_cases hv : v y = 0
    · simp [hv]
    rw [hagree x y hu hv, mul_assoc]
  rw [heq]
  calc
    _ ≤ (∑ x, ‖u x‖ * ‖applyKernel K v x‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using norm_sum_le (s := univ) (fun x => u x * applyKernel K v x)
    _ ≤ (∑ x, ‖u x‖^2) * ∑ x, ‖applyKernel K v x‖^2 :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by
      rw [mul_comm (M ^ 2), mul_assoc]
      exact mul_le_mul_of_nonneg_left (applyKernel_sum_sq K v hM) (by positivity)

#print axioms rectangle_bound

end ProximityGap.PaleyIntervalSpectrum
