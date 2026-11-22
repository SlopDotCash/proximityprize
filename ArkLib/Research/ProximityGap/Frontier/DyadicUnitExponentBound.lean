/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Bound on one cyclotomic-unit coordinate of a dyadic ratio comparison -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DyadicUnitExponentBound

/-- Each dyadic level supplies two translated signed weights at each center.
The coordinate of their difference is bounded by four per level. -/
theorem comparison_bound {G : Type*} [AddCommGroup G] {k : ℕ} (a : Fin k → G)
    (w : G → ℤ) (hw : ∀ j, |w j| ≤ 1) (x y : G) :
    |∑ i, (w (x + a i) + w (x - a i) - w (y + a i) - w (y - a i))| ≤ 4 * (k : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin k, (4 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      have h₁ := abs_le.mp (hw (x + a i))
      have h₂ := abs_le.mp (hw (x - a i))
      have h₃ := abs_le.mp (hw (y + a i))
      have h₄ := abs_le.mp (hw (y - a i))
      apply abs_le.mpr
      omega
    _ = _ := by simp [mul_comm]

/-- Switching all three nonzero sites to their inverses contributes a center-only factor. -/
theorem inverse_chord {F : Type*} [Field F] (x y z : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hyz : y ≠ z) :
    (x⁻¹ - z⁻¹) / (y⁻¹ - z⁻¹) = (y / x) * ((x-z)/(y-z)) := by
  have h₁ : y⁻¹ - z⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_injective.ne hyz)
  have h₂ : y-z ≠ 0 := sub_ne_zero.mpr hyz
  field_simp
  ring

/-- Inversion multiplies the comparison of a multiset locator by the center
factor raised to its total degree. -/
theorem inverse_locator_comparison {F ι : Type*} [Field F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (S : Finset ι) (z : ι → F) (m : ι → ℕ)
    (hz : ∀ i ∈ S, z i ≠ 0) (hyz : ∀ i ∈ S, y ≠ z i) :
    (∏ i ∈ S, ((x⁻¹ - (z i)⁻¹) / (y⁻¹ - (z i)⁻¹)) ^ m i) =
    (y / x) ^ (∑ i ∈ S, m i) * ∏ i ∈ S, ((x-z i)/(y-z i)) ^ m i := by
  calc
    _ = ∏ i ∈ S, ((y / x) ^ m i * ((x-z i)/(y-z i)) ^ m i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [inverse_chord x y (z i) hx hy (hz i hi) (hyz i hi), mul_pow]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

#print axioms inverse_locator_comparison
#print axioms comparison_bound
end ArkLib.ProximityGap.Frontier.DyadicUnitExponentBound
