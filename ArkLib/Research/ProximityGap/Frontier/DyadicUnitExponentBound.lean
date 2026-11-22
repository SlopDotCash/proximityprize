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

#print axioms comparison_bound
end ArkLib.ProximityGap.Frontier.DyadicUnitExponentBound
