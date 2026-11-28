/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Local intersection charges from a word outside a linear jet equation

The ordinary local colength bound gives a quadratic charge in the contact order.
Integer spacing strengthens its affine minorant on the support of an exterior word.
-/

namespace ProximityGap.LinearEquationContactBounds

/-- The integer quadratic has an extra charge below the contact level. -/
theorem integral_charge (o j I : ℤ) (h : o ^ 2 - o - 1 ≤ I) :
    2 * j * o + 2 * max (j - o) 0 ≤ I + j * (j + 1) + 1 := by
  by_cases ho : j ≤ o
  · rw [max_eq_right (by omega : j - o ≤ 0)]
    by_cases he : o = j
    · subst o
      nlinarith
    have hp := mul_nonneg (by omega : 0 ≤ o - j) (by omega : 0 ≤ o - j - 1)
    nlinarith
  · rw [max_eq_left (by omega : 0 ≤ j - o)]
    have hp := mul_nonneg (by omega : 0 ≤ j - o) (by omega : 0 ≤ j - o - 1)
    nlinarith

/-- Summing the local charges over a grid with an exterior agreement support. -/
theorem exterior_support {ι : Type*} (G S : Finset ι) (hS : S ⊆ G)
    (o I : ι → ℤ) (j D : ℤ)
    (hI : ∀ x ∈ G, o x ^ 2 - o x - 1 ≤ I x) (hD : ∑ x ∈ S, o x ≤ D) :
    2 * j * (∑ x ∈ G, o x) + 2 * (j * S.card - D) ≤
      (∑ x ∈ G, I x) + G.card * (j * (j + 1) + 1) := by
  classical
  have hc := Finset.sum_le_sum fun x (hx : x ∈ G) => integral_charge (o x) j (I x) (hI x hx)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hc
  have hs : ∑ x ∈ S, (j - o x) ≤ ∑ x ∈ G, max (j - o x) 0 := by
    calc
      _ ≤ ∑ x ∈ S, max (j - o x) 0 := Finset.sum_le_sum fun _ _ => le_max_left _ _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => le_max_right _ _
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  linarith [mul_comm j (S.card : ℤ)]

end ProximityGap.LinearEquationContactBounds

#print axioms ProximityGap.LinearEquationContactBounds.integral_charge
#print axioms ProximityGap.LinearEquationContactBounds.exterior_support
