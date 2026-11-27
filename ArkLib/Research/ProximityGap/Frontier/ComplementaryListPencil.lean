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

/-- When both pairs have the same double agreement, their parameter difference has
a double root at any site where the specialization coefficient is nonzero. -/
theorem square_dvd_parameter_difference {A B U V f g h i : F[X]} {x y : F}
    (sum_eq : f + g - (h + i) = A * (U - V))
    (product_eq : f * g - h * i = B * (U - V))
    (hf : f.eval x = y) (hg : g.eval x = y) (hh : h.eval x = y) (hi : i.eval x = y)
    (unit_at_site : B.eval x - y * A.eval x ≠ 0) :
    (X - C x) ^ 2 ∣ U - V := by
  have factor (q : F[X]) (hq : q.eval x = y) : X - C x ∣ q - C y :=
    dvd_iff_isRoot.mpr (by simp [IsRoot, hq])
  have diff : (f - C y) * (g - C y) - (h - C y) * (i - C y) =
      (B - C y * A) * (U - V) := by
    linear_combination product_eq - C y * sum_eq
  have cop : IsCoprime (X - C x) (B - C y * A) := by
    apply (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr
    intro hd
    exact unit_at_site (by simpa [IsRoot] using dvd_iff_isRoot.mp hd)
  apply cop.pow_left.dvd_of_dvd_mul_left
  rw [← diff, pow_two]
  exact dvd_sub (mul_dvd_mul (factor f hf) (factor g hg))
    (mul_dvd_mul (factor h hh) (factor i hi))

/-- Each common agreement costs one degree of the parameter difference. A shared
double agreement with nonzero specialization coefficient costs two. -/
theorem weighted_common_agreement_le [DecidableEq F] (sites double : Finset F)
    (center : F → F) {A B U V f g h i : F[X]} (distinct : U ≠ V)
    (sum_eq : f + g - (h + i) = A * (U - V))
    (product_eq : f * g - h * i = B * (U - V))
    (single : ∀ x ∈ sites, x ∉ double → U.eval x = V.eval x)
    (both : ∀ x ∈ sites, x ∈ double →
      f.eval x = center x ∧ g.eval x = center x ∧ h.eval x = center x ∧ i.eval x = center x ∧
      B.eval x - center x * A.eval x ≠ 0) :
    (∑ x ∈ sites, if x ∈ double then 2 else 1) ≤ (U - V).natDegree := by
  let weight (x : F) : ℕ := if x ∈ double then 2 else 1
  have divides : ∏ x ∈ sites, (X - C x) ^ weight x ∣ U - V := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow
    · intro x hx
      by_cases hd : x ∈ double
      · obtain ⟨hf, hg, hh, hi, hunit⟩ := both x hx hd
        simpa [weight, hd] using square_dvd_parameter_difference sum_eq product_eq hf hg hh hi hunit
      · simp only [weight, hd, ↓reduceIte, pow_one]
        exact dvd_iff_isRoot.mpr (by simp [IsRoot, single x hx hd])
  have bound := natDegree_le_of_dvd divides (sub_ne_zero.mpr distinct)
  rw [natDegree_prod_of_monic _ _ (fun x _ => (monic_X_sub_C x).pow (weight x))] at bound
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one, one_mul] using bound

#print axioms square_dvd_parameter_difference
#print axioms weighted_common_agreement_le
#print axioms determinant_zero
#print axioms common_product
#print axioms cross_product
end ProximityGap.ComplementaryListPencil
