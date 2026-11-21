/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Squarefree.Basic

/-! # A squarefree coordinate polynomial has a nonzero discriminant resultant

Work over the rational function field in the parameter. Coefficient-only factors become units.
Each positive-coordinate-degree irreducible factor remains irreducible by Gauss's lemma, and
is separable when its leading degree survives in the base field. -/

open Polynomial

namespace ProximityGap.SquarefreeCoordinateResultant

private theorem derivative_top {R : Type} [CommRing R] [IsDomain R] (p : R[X])
    (hd : 0 < p.natDegree) (hc : (p.natDegree : R) ≠ 0) :
    p.derivative ≠ 0 ∧ p.derivative.natDegree = p.natDegree - 1 := by
  have hx : p.natDegree - 1 + 1 = p.natDegree := by omega
  have hcoeff : p.derivative.coeff (p.natDegree - 1) ≠ 0 := by
    rw [coeff_derivative, ← Nat.cast_add_one, hx]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd)) hc
  exact ⟨fun h => hcoeff (by rw [h, coeff_zero]),
    le_antisymm (natDegree_derivative_le _) (le_natDegree_of_ne_zero hcoeff)⟩

variable {K : Type} [Field K]

private theorem separable_fraction (H : Polynomial K[X]) (hsq : Squarefree H)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ H.natDegree → (i : K) ≠ 0) :
    (H.map (algebraMap K[X] (FractionRing K[X]))).Separable := by
  classical
  let L := FractionRing K[X]
  let φ := algebraMap K[X] L
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  change (H.map φ).Separable
  induction H using WfDvdMonoid.induction_on_irreducible with
  | zero => exact False.elim (hsq.ne_zero rfl)
  | unit u hu =>
    obtain ⟨v, hv⟩ := hu.map (Polynomial.mapRingHom φ)
    change (↑v : L[X]) = u.map φ at hv
    change IsCoprime (u.map φ) _
    refine ⟨(↑v⁻¹ : L[X]), 0, ?_⟩
    rw [← hv]
    simp
  | mul z p hz hp ih =>
    have hl := squarefree_mul_iff.mp hsq
    have hsum : (p * z).natDegree = p.natDegree + z.natDegree := natDegree_mul hp.ne_zero hz
    have hsep := ih hl.2.2 (fun i hi hle => hchar i hi (by rw [hsum]; omega))
    rw [Polynomial.map_mul]
    by_cases hdeg : p.natDegree = 0
    · have hconst := eq_C_of_natDegree_eq_zero hdeg
      have hc : p.coeff 0 ≠ 0 := by
        intro h
        exact hp.ne_zero (hconst.trans (by rw [h, C_0]))
      apply Separable.unit_mul _ hsep
      rw [hconst, Polynomial.map_C]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun h => hc (hinj (h.trans (map_zero φ).symm)))
    · have hprim := hp.isPrimitive hdeg
      have hirr := (hprim.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hp
      have hcop := (hirr.isCoprime_or_dvd (z.map φ)).resolve_right
        (fun h => (hp.isRelPrime_iff_not_dvd.mp hl.1)
          ((hprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr h))
      have hcast : (p.natDegree : K) ≠ 0 :=
        hchar _ (Nat.pos_of_ne_zero hdeg) (by rw [hsum]; omega)
      have hpoly : (p.natDegree : K[X]) ≠ 0 := by rwa [← C_eq_natCast, Ne, C_eq_zero]
      have hcast' : (p.natDegree : L) ≠ 0 := by
        simpa only [map_natCast] using (show φ (p.natDegree : K[X]) ≠ 0 from
          fun h => hpoly (hinj (h.trans (map_zero φ).symm)))
      have hmap := natDegree_map_eq_of_injective hinj (p := p)
      apply Separable.mul _ hsep hcop
      apply (separable_iff_derivative_ne_zero hirr).mpr
      apply (derivative_top _ (by rw [hmap]; omega) (by rwa [hmap])).1

/-- A squarefree bivariate polynomial of positive coordinate degree has a nonzero
coordinate resultant when all positive degrees up to that degree survive in the field. -/
theorem squarefree_resultant_ne_zero (H : Polynomial K[X]) (hsq : Squarefree H)
    (hpos : 0 < H.natDegree)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ H.natDegree → (i : K) ≠ 0) :
    resultant H H.derivative H.natDegree (H.natDegree - 1) ≠ 0 := by
  let L := FractionRing K[X]
  let φ := algebraMap K[X] L
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hs := separable_fraction H hsq hchar
  change IsCoprime (H.map φ) (H.map φ).derivative at hs
  rw [derivative_map] at hs
  have hr := Polynomial.resultant_ne_zero _ _ hs
  have hc : (H.natDegree : K[X]) ≠ 0 := by
    rw [← C_eq_natCast, Ne, C_eq_zero]
    exact hchar _ hpos le_rfl
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map, (derivative_top H hpos hc).2] at hr
  exact fun h => hr (by rw [h, map_zero])

#print axioms squarefree_resultant_ne_zero

end ProximityGap.SquarefreeCoordinateResultant
