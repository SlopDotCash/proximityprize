/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic

/-! # Removing the generic common factor of two ordinary polar resultants

Over a coordinate polynomial ring, one may remove the primitive integral
representative of the fraction-field gcd. The quotients remain integral and
are coprime over the fraction field, so their own resultant detects all
specialization rank losses without selecting a generic minor.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped nonZeroDivisors

namespace ArkLib.ProximityGap.Frontier.IntegralCommonPolar

variable {R L : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- A primitive integral representative of a nonzero fraction-field
polynomial, with the same degree and associated generic fiber. -/
theorem primitive_representative (D : L[X]) (hD : D ≠ 0) :
    ∃ E : R[X], E.IsPrimitive ∧ E.natDegree = D.natDegree ∧
      Associated (E.map (algebraMap R L)) D := by
  classical
  let N := IsLocalization.integerNormalization R⁰ D
  have hn : N ≠ 0 := IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hD
  obtain ⟨b,hb,hbD⟩ := IsLocalization.integerNormalization_spec R⁰ D
  let φ := algebraMap R L
  have hφ := IsFractionRing.injective R L
  have hb0 : φ b ≠ 0 := (map_ne_zero_iff _ hφ).mpr (nonZeroDivisors.ne_zero hb)
  have hc0 : φ N.content ≠ 0 := (map_ne_zero_iff _ hφ).mpr (content_eq_zero_iff.not.mpr hn)
  have hE : N.primPart.map φ ≠ 0 := by simpa using (map_injective φ hφ).ne (primPart_ne_zero N)
  have H : C (φ N.content) * N.primPart.map φ = C (φ b)*D := by
    rw [← map_C φ, ← Polynomial.map_mul, ← N.eq_C_content_mul_primPart]
    simpa [N,φ,Algebra.smul_def,Polynomial.algebraMap_apply] using hbD
  have hass : Associated (N.primPart.map φ) D := by
    have h := Associated.of_eq H
    rw [mul_comm (C (φ N.content)), mul_comm (C (φ b)),
      associated_mul_isUnit_left_iff (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)),
      associated_mul_isUnit_right_iff (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0))] at h
    exact h
  refine ⟨N.primPart,isPrimitive_primPart _,?_,hass⟩
  rw [← natDegree_map_eq_of_injective hφ N.primPart]
  exact le_antisymm (natDegree_le_of_dvd hass.dvd hD) (natDegree_le_of_dvd hass.symm.dvd hE)

/-- The generic gcd has an integral primitive representative whose removal
leaves a coprime pair, including common scalar-only contents in either quotient. -/
theorem remove_generic_gcd [DecidableEq L] (A B : R[X]) (hA : A ≠ 0) :
    ∃ E F G : R[X], E.IsPrimitive ∧ A = E*F ∧ B = E*G ∧
      E.natDegree = (GCDMonoid.gcd (A.map (algebraMap R L)) (B.map (algebraMap R L))).natDegree ∧
      IsCoprime (F.map (algebraMap R L)) (G.map (algebraMap R L)) := by
  classical
  let φ := algebraMap R L
  let D := GCDMonoid.gcd (A.map φ) (B.map φ)
  have hA' : A.map φ ≠ 0 := by simpa using (map_injective φ (IsFractionRing.injective R L)).ne hA
  have hD : D ≠ 0 := gcd_ne_zero_of_left hA'
  obtain ⟨E,hp,hd,ha⟩ := primitive_representative (R := R) D hD
  obtain ⟨F,hF⟩ := hp.dvd_of_fraction_map_dvd_fraction_map (ha.dvd.trans (gcd_dvd_left ..))
  obtain ⟨G,hG⟩ := hp.dvd_of_fraction_map_dvd_fraction_map (ha.dvd.trans (gcd_dvd_right ..))
  refine ⟨E,F,G,hp,hF,hG,hd,?_⟩
  have hn : E.map φ ≠ 0 := by simpa using (map_injective φ (IsFractionRing.injective R L)).ne hp.ne_zero
  have hf : A.map φ = E.map φ * F.map φ := by rw [hF,Polynomial.map_mul]
  have hg : B.map φ = E.map φ * G.map φ := by rw [hG,Polynomial.map_mul]
  have hmul : Associated D (E.map φ * GCDMonoid.gcd (F.map φ) (G.map φ)) := by
    change Associated (GCDMonoid.gcd (A.map φ) (B.map φ)) _
    rw [hf,hg]
    exact gcd_mul_left' ..
  have hcancel : Associated (E.map φ * 1) (E.map φ * GCDMonoid.gcd (F.map φ) (G.map φ)) := by
    simpa using ha.trans hmul
  exact (gcd_isUnit_iff _ _).mp ((hcancel.of_mul_left (Associated.refl _) hn).isUnit isUnit_one)

#print axioms primitive_representative
#print axioms remove_generic_gcd

end ArkLib.ProximityGap.Frontier.IntegralCommonPolar
