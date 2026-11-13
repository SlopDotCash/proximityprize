/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# AJT13: the annihilator Jacobi tensor is the centered fourteenth moment

For a subgroup of size `n` in a field of size `q`, put `m = (q - 1) / n`.  Removing the
principal multiplicative character centers each Gauss period `eta` by its exact nonzero-frequency
mean `-1 / m`.  Fourteen-fold character orthogonality therefore identifies the proposed
all-nontrivial thirteen-variable Jacobi socket with

`m^13 / q^7 * sum_b (eta_b + 1 / m)^14`.

This file records the normalization and budget algebra after that orthogonality step.  In
particular, the suggested `m^7` socket is not a dimension-reducing estimate: at the exact
coefficient forced by `q - 1 = n*m`, it is equivalent to the centered physical-space
fourteenth-moment bound `sum_b (...)^14 <= C*q*n^6`.  The full uncentered moment still needs the
principal-character boundary terms (equivalently, undoing the shift by `1/m`).

No Jacobi bound or cancellation input is asserted here.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence

/-- The centered physical-space fourteenth moment produced by deleting the principal
multiplicative character. -/
noncomputable def centeredPeriodMoment14 {I : Type*} [Fintype I]
    (m : ℝ) (eta : I → ℝ) : ℝ :=
  ∑ i : I, (eta i + 1 / m) ^ 14

/-- The character tensor is a positive moment after full orthogonality; it is not an
indefinite correlation on which positivity-blind cancellation can be obtained for free. -/
theorem centeredPeriodMoment14_nonneg {I : Type*} [Fintype I]
    (m : ℝ) (eta : I → ℝ) :
    0 ≤ centeredPeriodMoment14 m eta := by
  unfold centeredPeriodMoment14
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- The normalization of the all-nontrivial fourteen-Gauss-product correlation after one
character has been eliminated by the product constraint.  The remaining sum is indexed by
thirteen freely chosen nontrivial characters, hence the name `tensor13Socket`. -/
noncomputable def tensor13Socket (m q Y : ℝ) : ℝ :=
  m ^ 13 / q ^ 7 * Y

/-- Positivity of the normalized socket in its actual centered-moment realization. -/
theorem tensor13Socket_centered_nonneg {I : Type*} [Fintype I]
    {m q : ℝ} (hm : 0 ≤ m) (hq : 0 < q) (eta : I → ℝ) :
    0 ≤ tensor13Socket m q (centeredPeriodMoment14 m eta) := by
  unfold tensor13Socket
  exact mul_nonneg (by positivity) (centeredPeriodMoment14_nonneg m eta)

/-- **Exact production-scale normalization.**  If `q - 1 = n*m`, multiplying the centered
period-moment budget `C*q*n^6` by the Jacobi normalization gives precisely
`C*m^7*((q-1)/q)^6`. -/
theorem tensor13_scale_eq {n m q C : ℝ} (hm : m ≠ 0) (hq : q ≠ 0)
    (hindex : q - 1 = n * m) :
    m ^ 13 / q ^ 7 * (C * q * n ^ 6) =
      C * m ^ 7 * ((q - 1) / q) ^ 6 := by
  rw [hindex]
  field_simp

/-- **The `m^7` Jacobi socket is exactly the centered fourteenth-moment wall.**  This is the
inequality form of `tensor13_scale_eq`: the positive normalization can be cancelled with no
loss.  Consequently, character orthogonality in all thirteen free variables only changes
coordinates; it does not supply cancellation beyond the original centered moment. -/
theorem tensor13Socket_le_iff_centeredMoment_le {n m q C Y : ℝ}
    (hm : 0 < m) (hq : 0 < q) (hindex : q - 1 = n * m) :
    tensor13Socket m q Y ≤ C * m ^ 7 * ((q - 1) / q) ^ 6 ↔
      Y ≤ C * q * n ^ 6 := by
  have hscale :
      C * m ^ 7 * ((q - 1) / q) ^ 6 =
        m ^ 13 / q ^ 7 * (C * q * n ^ 6) :=
    (tensor13_scale_eq (C := C) (ne_of_gt hm) (ne_of_gt hq) hindex).symm
  rw [tensor13Socket, hscale]
  have hfac : 0 < m ^ 13 / q ^ 7 := by positivity
  exact mul_le_mul_iff_of_pos_left hfac

/-- Restoring the coefficient of the top character stratum turns its normalized Jacobi
socket back into `n` times the centered moment.  Thus the apparent thirteen-dimensional
tensor contribution is literally the nonzero-frequency centered moment in Fourier coordinates. -/
theorem topStratumCoefficient_mul_socket {n m q Y : ℝ}
    (hm : m ≠ 0) (hq : q ≠ 0) (hindex : q - 1 = n * m) :
    ((q - 1) * q ^ 7 / m ^ 14) * tensor13Socket m q Y = n * Y := by
  rw [tensor13Socket, hindex]
  field_simp

/-- The intended Wick constant leaves genuine room below the public `2^18` coefficient. -/
theorem wick13_lt_publicCoefficient : (135135 : ℝ) < 2 ^ 18 := by
  norm_num

/-- A concrete arithmetic warning: an aligned phase array can have the correct second-moment
scale while its fourteenth moment is far above the `2^18*m^7` socket.  Hence cyclic product
geometry and coefficient moduli alone cannot prove the desired tensor estimate.  (`m = 64`
is merely a small exact witness to the exponent gap.) -/
theorem aligned_secondMoment_has_exact_scale :
    (((63 : ℝ) ^ 2 + 63) / 64) = 63 := by
  norm_num

theorem aligned_fourteenthMoment_exceeds_publicCoefficient :
    (((63 : ℝ) ^ 14 + 63) / 64) > 2 ^ 18 * (64 : ℝ) ^ 7 := by
  norm_num

end ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.centeredPeriodMoment14_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.tensor13Socket_centered_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.tensor13_scale_eq
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.tensor13Socket_le_iff_centeredMoment_le
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.topStratumCoefficient_mul_socket
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.aligned_secondMoment_has_exact_scale
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredMomentEquivalence.aligned_fourteenthMoment_exceeds_publicCoefficient
