/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Reflection of weighted locator logarithms and their squared energies -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DyadicLocatorReflection

/-- A weighted sum of translates of an even logarithm table on the exponent group. -/
def evaluation {G A : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup A]
    (a : G → A) (w : G → ℤ) (x : G) : A := ∑ j, w j • a (j - x)

/-- Negating the exponents in the weights negates the center of evaluation. -/
theorem evaluation_reflect {G A : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup A]
    (a : G → A) (ha : ∀ j, a (-j) = a j) (w : G → ℤ) (x : G) :
    evaluation a (fun j => w (-j)) x = evaluation a w (-x) := by
  unfold evaluation
  apply Fintype.sum_equiv (Equiv.neg G)
  intro j
  change w (-j) • a (j-x) = w (-j) • a (-j - -x)
  rw [show -j - -x = -(j-x) by abel, ha]

/-- Constant values at three reflected sites give zero differences in both signed sectors. -/
theorem reflection_differences {G A : Type*} [Fintype G] [AddCommGroup G] [AddCommGroup A]
    (a : G → A) (ha : ∀ j, a (-j) = a j) (w : G → ℤ) (x : G)
    (hx : evaluation a w x = evaluation a w 0) (hn : evaluation a w (-x) = evaluation a w 0) :
    evaluation a (fun j => w j + w (-j)) x = evaluation a (fun j => w j + w (-j)) 0 ∧
    evaluation a (fun j => w j - w (-j)) x = evaluation a (fun j => w j - w (-j)) 0 := by
  have hr (y : G) := evaluation_reflect a ha w y
  constructor
  · simp only [evaluation, add_zsmul, Finset.sum_add_distrib]
    change evaluation a w x + evaluation a (fun j => w (-j)) x =
      evaluation a w 0 + evaluation a (fun j => w (-j)) 0
    rw [hr x, hr 0, neg_zero, hx, hn]
  · simp only [evaluation, sub_zsmul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
    change evaluation a w x - evaluation a (fun j => w (-j)) x =
      evaluation a w 0 - evaluation a (fun j => w (-j)) 0
    rw [hr x, hr 0, neg_zero, hx, hn]

/-- The symmetric source has fixed-site weight `2*c`. In its metric the fixed
coordinate has coefficient one half. Twice the sum of the compressed energies
equals four times the full source energy. -/
theorem reflection_energy {I : Type*} [Fintype I] (u v : I → ℤ) (c : ℤ) :
    (2 * (∑ i, (u i + v i)^2) + (2*c)^2) + 2 * (∑ i, (u i - v i)^2) =
      4 * ((∑ i, ((u i)^2 + (v i)^2)) + c^2) := by
  have he : (∑ i, (u i + v i)^2) + ∑ i, (u i - v i)^2 =
      2 * (∑ i, ((u i)^2 + (v i)^2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- At least one compressed vector lies in its certifying ball whenever the
original source has squared energy at most `B`. -/
theorem one_sector_short {I : Type*} [Fintype I] (u v : I → ℤ) (c B : ℤ)
    (h : (∑ i, ((u i)^2 + (v i)^2)) + c^2 ≤ B) :
    2 * (∑ i, (u i + v i)^2) + (2*c)^2 ≤ 2*B ∨ (∑ i, (u i - v i)^2) ≤ B := by
  have he := reflection_energy u v c
  omega

/-- Multiplying at antipodes folds a locator factor to the squared domain. -/
theorem antipodal_factor {R : Type*} [CommRing R] (x a : R) :
    (x-a)*(-x-a) = -(x^2-a^2) := by ring

/-- The residual factor after opposite weights have been recovered. Its value
at the antipode is the reciprocal of its original value. -/
theorem antipodal_quotient {K : Type*} [Field K] (x a : K) :
    (-x-a)/(-x+a) = ((x-a)/(x+a))⁻¹ := by
  rw [inv_div]
  rw [show -x-a = -(x+a) by ring, show -x+a = -(x-a) by ring, neg_div_neg_eq]

#print axioms reflection_differences
#print axioms one_sector_short
#print axioms antipodal_factor
#print axioms antipodal_quotient
end ArkLib.ProximityGap.Frontier.DyadicLocatorReflection
