/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # A quadratic bound on simultaneous dyadic unit exponents -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DyadicUnitEllipsoid

/-- For a matrix A, whenever A Aᵀ y = A w, the projected energy yᵀ A w
is bounded by wᵀ w. This form avoids any invertibility hypothesis. -/
theorem projected_energy {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℚ)
    (w : J → ℚ) (y : I → ℚ)
    (hy : ∀ i, ∑ j, A i j * (∑ k, y k * A k j) = ∑ j, A i j * w j) :
    ∑ i, y i * (∑ j, A i j * w j) ≤ ∑ j, (w j) ^ 2 := by
  let u (j : J) := ∑ i, y i * A i j
  have adj (v : J → ℚ) : (∑ j, v j * u j) = ∑ i, y i * (∑ j, A i j * v j) := by
    dsimp [u]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h₁ := adj u
  simp only [u, hy] at h₁
  have h₂ := adj w
  have pos : 0 ≤ ∑ j, (w j - u j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have expand : (∑ j, (w j - u j) ^ 2) =
      (∑ j, (w j) ^ 2) - 2 * (∑ j, w j * u j) + (∑ j, u j * u j) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  change (∑ j, u j * u j) = ∑ i, y i * (∑ j, A i j * w j) at h₁
  linarith

/-- Squared volume comparison using π > 3, for the displacement-two
order-256 ellipsoid and the larger named prime. -/
theorem order256_volume_comparison :
    (2^64 * ((730750818665451459101842416358141509841924915201 - 1) / 256) *
      2 * Nat.factorial 32)^2 <
    (3 * 74)^64 * 614560623940147206055138107999571273706286146912256 := by decide

#print axioms order256_volume_comparison
#print axioms projected_energy
end ArkLib.ProximityGap.Frontier.DyadicUnitEllipsoid
