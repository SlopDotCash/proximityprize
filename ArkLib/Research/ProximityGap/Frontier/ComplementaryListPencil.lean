/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! # Polynomial pencils from pairs covering one received word -/

namespace ProximityGap.ComplementaryListPencil
open Polynomial
variable {F : Type*} [Field F]

/-- Three monic quadratics with a common ordinate on more sites than the determinant's
degree have collinear sum and product coefficients over the rational function field. -/
theorem determinant_zero (s₀ s₁ s₂ p₀ p₁ p₂ : F[X]) (T : Finset F) (y : F → F) {d : ℕ}
    (hs₀ : s₀.natDegree ≤ d) (hs₁ : s₁.natDegree ≤ d) (hs₂ : s₂.natDegree ≤ d)
    (hp₀ : p₀.natDegree ≤ 2 * d) (hp₁ : p₁.natDegree ≤ 2 * d) (hp₂ : p₂.natDegree ≤ 2 * d)
    (size : 3 * d < T.card)
    (hit : ∀ x ∈ T, p₀.eval x = s₀.eval x * y x - y x ^ 2 ∧
      p₁.eval x = s₁.eval x * y x - y x ^ 2 ∧ p₂.eval x = s₂.eval x * y x - y x ^ 2) :
    (s₁ - s₀) * (p₂ - p₀) - (s₂ - s₀) * (p₁ - p₀) = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T
  · intro x hx
    obtain ⟨h₀, h₁, h₂⟩ := hit x hx
    simp only [eval_sub, eval_mul, h₀, h₁, h₂]
    ring
  · have h₁ := (natDegree_sub_le s₁ s₀).trans (max_le hs₁ hs₀)
    have h₂ := (natDegree_sub_le s₂ s₀).trans (max_le hs₂ hs₀)
    have g₁ := (natDegree_sub_le p₁ p₀).trans (max_le hp₁ hp₀)
    have g₂ := (natDegree_sub_le p₂ p₀).trans (max_le hp₂ hp₀)
    exact (natDegree_sub_le ..).trans_lt (max_lt
      (natDegree_mul_le.trans_lt (by omega : (s₁ - s₀).natDegree + (p₂ - p₀).natDegree < T.card))
      (natDegree_mul_le.trans_lt (by omega : (s₂ - s₀).natDegree + (p₁ - p₀).natDegree < T.card)))

/-- The two linear factors in every member give divisors of one fixed polynomial. -/
theorem common_product {R : Type*} [CommRing R] (A B S P U f g : R)
    (sum_eq : f + g = S + A * U) (product_eq : f * g = P + B * U) :
    (A * f - B) * (A * g - B) = B ^ 2 - S * A * B + P * A ^ 2 := by
  linear_combination A ^ 2 * product_eq - A * B * sum_eq

/-- The four cross-differences account for the two copies of the parameter difference
and the fixed polynomial, including at zeros of the leading parameter coefficient. -/
theorem cross_product {R : Type*} [CommRing R] (A B U f g h i : R)
    (sum_eq : f + g - (h + i) = A * U) (product_eq : f * g - h * i = B * U) :
    (f - h) * (g - h) * (f - i) * (g - i) = U ^ 2 * ((A * h - B) * (A * i - B)) := by
  have hh : (f - h) * (g - h) = U * (B - A * h) := by
    linear_combination product_eq - h * sum_eq
  have hi : (f - i) * (g - i) = U * (B - A * i) := by
    linear_combination product_eq - i * sum_eq
  calc
    _ = ((f - h) * (g - h)) * ((f - i) * (g - i)) := by ring
    _ = _ := by rw [hh, hi]; ring

#print axioms determinant_zero
#print axioms common_product
#print axioms cross_product
end ProximityGap.ComplementaryListPencil
