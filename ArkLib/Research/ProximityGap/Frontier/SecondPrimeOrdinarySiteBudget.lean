/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSeparableDifferential
import ArkLib.Research.ProximityGap.Frontier.CubicPolarSiteBudget
import ArkLib.Research.ProximityGap.Frontier.IntrinsicReceivedSections
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.FieldTheory.IsSepClosed

/-! # Descent of the ordinary-polar sheet budget to the genuine coefficient field -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeOrdinarySiteBudget

open Polynomial Finset
open scoped Differential
open GenericProjectivePolarGcd JetMultiplierGraph TruncatedJetMultipliers ReceivedPolarContacts
open CanonicalQuarticSiteOrder ScalarHessianLocalOrder

set_option maxRecDepth 4096

variable {K L k : Type} [Field K] [Field L] [Field k]
noncomputable local instance [Differential K] : Differential K[X] := ⟨Differential.mapCoeffs⟩

private theorem primitive_map (φ : K →+* L) (F : K[X][X]) (hp : F.IsPrimitive) :
    (mapPlane φ F).IsPrimitive := by
  classical
  apply isPrimitive_of_contentIdeal_eq_top
  rw [mapPlane, contentIdeal_map_eq_map_contentIdeal, (isPrimitive_iff_contentIdeal_eq_top _).mp hp,
    Ideal.map_top]

private theorem map_dx (φ : K →+* L) (F : K[X][X]) : mapPlane φ (dx F) = dx (mapPlane φ F) := by
  ext1 i
  simp only [mapPlane, coeff_map, coe_mapRingHom, coeff_dx, derivative_map]

private theorem map_polar (φ : K →+* L) (F : K[X][X]) (c : K) :
    mapPlane φ (polar (dx F) F.derivative c) = polar (dx (mapPlane φ F))
      (mapPlane φ F).derivative (φ c) := by
  simp only [polar, mapPlane, Polynomial.map_add, Polynomial.map_mul, map_C, coe_mapRingHom,
    ← derivative_map]
  exact congrArg (fun A => A + _) (map_dx φ F)

private theorem map_hess [Differential K] [Differential L] (φ : K →+* L)
    (hφ : ∀ a, φ a′ = (φ a)′) (F : K[X][X]) : mapPlane φ (hessian F) = hessian (mapPlane φ F) := by
  apply ReceivedPowerSeriesHessian.hessian_map
  intro a
  ext i
  simp only [coe_mapRingHom, coeff_map]
  change φ (a.coeff i)′ = ((a.map φ).coeff i)′
  rw [coeff_map]
  exact hφ _

private theorem lift_leader (φ : K →+* L) {F : K[X][X]} {r j : ℕ}
    (h : Leader F r j) : Leader (mapPlane φ F) r j := by
  refine ⟨h.value_le, ?_, fun i v hh => ?_⟩
  · simpa only [mapPlane, coeff_map, coe_mapRingHom, _root_.map_ne_zero] using h.nonzero
  · simp only [mapPlane, coeff_map, coe_mapRingHom, h.lower i v hh, map_zero]

private theorem received_leader (φ : K →+* L) (F : K[X][X]) (hf : F.IsPrimitive) (a l : K) :
    ∃ i, Leader (ReceivedJetContact.shifted (mapPlane φ F) (φ a) (φ l))
      (siteOrder F a (C l)) i := by
  obtain ⟨i, hi⟩ := exists_leader_at_site F hf a (C l)
  refine ⟨i, ?_⟩
  have h := lift_leader φ hi
  change Leader (mapPlane φ (shift F a l)) _ i at h
  rw [mapPlane_shift] at h
  have hh (G : L[X][X]) (x y : L) : shift G x y = ReceivedJetContact.shifted G x y := by
    rw [shift, ReceivedJetContact.shifted, map_taylor]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, taylorAlgHom_apply, taylor_C]
  rwa [hh] at h

/-- A second slope in the actual infinite constant field yields the sheet budget on the original
received sites, with the gcd measured over the original scalar field. All projective sheets,
extension of the derivation, and local leaders are supplied inside the proof. -/
theorem raw_budget [Differential K] [Infinite k] [DecidableEq K] (φ : k →+* K)
    (p : ℕ) [CharP K p] (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (F : K[X][X]) (hb : F.natDegree = 3) (hp : F.IsPrimitive)
    (hV : F.resultant F.derivative 3 3 ≠ 0) (hH : F.resultant (hessian F) 3 7 ≠ 0)
    (A : K[X]) (hA : A ≠ 0) (hAp : A.natDegree < p) (except : Finset k)
    (D : Finset K) (l : K → K) (hD : ∀ a ∈ D, a′ = 0) (hl : ∀ a ∈ D, (l a)′′ = 0) :
    ∃ c ∉ except, let B := F.resultant (polar (dx F) F.derivative (φ c)) 3 3
      B ≠ 0 ∧ 3 * (∑ a ∈ D, siteOrder F a (C (l a))) + 2 * (GCDMonoid.gcd A B).natDegree ≤
        2 * D.card + 4 * F.leadingCoeff.natDegree + (F.resultant (hessian F) 3 7).natDegree := by
  classical
  let E := SeparableClosure K
  let _ : Differential E := SecondPrimeSeparableDifferential.extension (K := K)
  let _ : DifferentialAlgebra K E := SecondPrimeSeparableDifferential.compatible
  let ψ := algebraMap K E
  let _ : Infinite E := Infinite.of_injective (ψ.comp φ) (ψ.comp φ).injective
  let e : K ↪ E := ⟨ψ, ψ.injective⟩
  let inv := Function.invFun e
  have hinv (a : K) : inv (e a) = a := Function.leftInverse_invFun e.injective a
  have hφ (a : K) : ψ a′ = (ψ a)′ := (deriv_algebraMap a).symm
  let F' := mapPlane ψ F
  let r (a : K) := siteOrder F a (C (l a))
  have p₀ : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  let _ : CharP E p := p₀
  have e₂ : (2 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ψ).mpr h₂
  have e₃ : (3 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero ψ).mpr h₃
  have hbase (Q : K[X][X]) (h : ℕ) :
      F'.resultant (mapPlane ψ Q) 3 h = (F.resultant Q 3 h).map ψ := resultant_map_map ..
  have hd' : F'.natDegree = 3 :=
    (natDegree_map_eq_of_injective (Polynomial.map_injective _ ψ.injective) F).trans hb
  have hV' : F'.resultant F'.derivative 3 3 ≠ 0 := by
    change F'.resultant (mapPlane ψ F).derivative 3 3 ≠ 0
    rw [show (mapPlane ψ F).derivative = mapPlane ψ F.derivative from derivative_map _ _, hbase]
    exact (Polynomial.map_ne_zero_iff ψ.injective).mpr hV
  have hH' : F'.resultant (hessian F') 3 7 ≠ 0 := by
    rw [show hessian F' = mapPlane ψ (hessian F) from (map_hess ψ hφ F).symm, hbase]
    exact (Polynomial.map_ne_zero_iff ψ.injective).mpr hH
  obtain ⟨c, hc, hB, hraw⟩ := CubicPolarSiteBudget.cubic_site_budget (ψ.comp φ) p e₂ e₃ F'
    hd' (primitive_map ψ F hp) hV' hH' (A.map ψ) ((Polynomial.map_ne_zero_iff ψ.injective).mpr hA)
    (by rwa [natDegree_map_eq_of_injective ψ.injective]) except (D.map e) (fun b => ψ (l (inv b)))
    (fun b => r (inv b)) (by
      intro b hb'
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hb'
      rw [hinv]
      exact ⟨by change (ψ a)′ = 0; rw [← hφ, hD a ha, map_zero],
        by rw [← hφ, ← hφ, hl a ha, map_zero], received_leader ψ F hp a (l a)⟩)
  let B := F.resultant (polar (dx F) F.derivative (φ c)) 3 3
  have hB' : F'.resultant (polar (dx F') F'.derivative ((ψ.comp φ) c)) 3 3 = B.map ψ := by
    rw [← hbase, map_polar]
    rfl
  have hne : B ≠ 0 := by
    intro hz
    exact hB (by rw [hB', hz, Polynomial.map_zero])
  have hgc : (GCDMonoid.gcd A B).map ψ ∣ GCDMonoid.gcd (A.map ψ) (B.map ψ) :=
    dvd_gcd (map_dvd (mapRingHom ψ) (gcd_dvd_left A B)) (map_dvd (mapRingHom ψ) (gcd_dvd_right A B))
  have hn' : GCDMonoid.gcd (A.map ψ) (B.map ψ) ≠ 0 :=
    ne_zero_of_dvd_ne_zero ((Polynomial.map_ne_zero_iff ψ.injective).mpr hA) (gcd_dvd_left ..)
  have hcdeg := Polynomial.natDegree_le_of_dvd hgc hn'
  rw [natDegree_map_eq_of_injective ψ.injective] at hcdeg
  have hlc : F'.leadingCoeff.natDegree = F.leadingCoeff.natDegree := by
    change (F.map (mapRingHom ψ)).leadingCoeff.natDegree = _
    rw [leadingCoeff_map_of_injective (Polynomial.map_injective _ ψ.injective)]
    exact natDegree_map_eq_of_injective ψ.injective _
  have hess := map_hess ψ hφ F
  change mapPlane ψ (hessian F) = hessian F' at hess
  have hdeq : (F'.resultant (hessian F') 3 7).natDegree =
      (F.resultant (hessian F) 3 7).natDegree := by
    rw [← hess, hbase, natDegree_map_eq_of_injective ψ.injective]
  simp only [hB', Finset.sum_map, Finset.card_map, hlc, hdeq, hinv] at hraw
  exact ⟨c, hc, hne, (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hcdeg) _).trans hraw⟩

#print axioms raw_budget
end ArkLib.ProximityGap.Frontier.SecondPrimeOrdinarySiteBudget
