/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.IntegralSectionChart
import ArkLib.Research.ProximityGap.Frontier.PolynomialLocalOrder
import ArkLib.Research.ProximityGap.Frontier.TerminalQuarticHessianTransport
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Primitivity of the cleared coordinate chart

At a nonzero new coordinate, invert the change of coordinate on the old
primitive equation. At zero a coefficient attaining the full weight has its
old leading coefficient as its value. This accounts for every possible
coordinate factor, including one hidden at the old coordinate infinity.
-/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace ArkLib.ProximityGap.Frontier.PrimitiveIntegralSectionChart
open IntegralSectionChart _root_.ProximityGap.CommonSectionChart

variable {k L E : Type} [Field k] [Field L] [Field E]

/-- The integral coordinate change commutes with an arbitrary scalar homomorphism. -/
theorem map_slot (φ : k[X] →+* L) (F : k[X][X][X]) (r : k) (w d j : ℕ) :
    ((chart r w d F).coeff j).map φ =
      change (φ (C r)) (w-d*j) ((F.coeff j).map φ) := by
  simp only [coeff_chart,← reflect_map,map_taylor,change]

/-- A nonzero coefficient exists at every geometric coordinate, including the
special coordinate zero above the old site at infinity. -/
theorem nonvanishing (φ : k[X] →+* L) (hφ : Function.Injective φ)
    (F : k[X][X][X]) (r : k) (w d : ℕ)
    (hprim : (F.map (mapRingHom φ)).IsPrimitive)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (htop : ∃ j, F.coeff j ≠ 0 ∧ (F.coeff j).natDegree+d*j = w)
    (ρ : L →+* E) (u : E) :
    ∃ j, ((((chart r w d F).coeff j).map φ).map ρ).eval u ≠ 0 := by
  let σ := ρ.comp φ
  let s := σ (C r)
  by_cases hu : u=0
  · subst u
    obtain ⟨j,hj,he⟩ := htop
    refine ⟨j,?_⟩
    rw [Polynomial.map_map,map_slot]
    change (change s (w-d*j) ((F.coeff j).map σ)).eval 0 ≠ 0
    have hinj := ρ.injective.comp hφ
    have hn : ((F.coeff j).map σ).natDegree = w-d*j := by
      rw [natDegree_map_eq_of_injective hinj]; omega
    rw [change,← coeff_zero_eq_eval_zero,coeff_reflect,revAt_zero,← hn,coeff_taylor_natDegree]
    exact leadingCoeff_ne_zero.mpr (by simpa [σ] using (map_injective σ hinj).ne hj)
  · let x := u⁻¹+s
    let f := F.map (mapRingHom φ)
    let ψ := eval₂RingHom ρ x
    have h := PolynomialLocalOrder.primitive_map_ne_zero f hprim ψ
    obtain ⟨j,hj⟩ : ∃ j, (f.map ψ).coeff j ≠ 0 := by
      by_contra! hall
      exact h (Polynomial.ext (by simpa using hall))
    have hold : ((F.coeff j).map σ).eval x ≠ 0 := by
      rw [Polynomial.coeff_map,show f.coeff j = (F.coeff j).map φ from Polynomial.coeff_map ..] at hj
      change ((F.coeff j).map φ).eval₂ ρ x ≠ 0 at hj
      rw [eval₂_eq_eval_map,Polynomial.map_map] at hj
      exact hj
    have hn : F.coeff j ≠ 0 := fun hz => hold (by simp [hz])
    have hdeg : ((F.coeff j).map σ).natDegree ≤ w-d*j := natDegree_map_le.trans (by have := hW j hn; omega)
    refine ⟨j,?_⟩
    rw [Polynomial.map_map,map_slot]
    change (change s (w-d*j) ((F.coeff j).map σ)).eval u ≠ 0
    have hx : x ≠ s := by dsimp [x]; simpa using inv_ne_zero hu
    have hux : (x-s)⁻¹=u := by simp [x]
    rw [← hux,eval_site s x _ _ hdeg hx]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr hx))) hold

/-- The geometric full-weight criterion gives primitivity over the original
scalar function field, before adjoining any roots. -/
theorem primitive (φ : k[X] →+* L) (hφ : Function.Injective φ)
    (F : k[X][X][X]) (r : k) (w d : ℕ)
    (hprim : (F.map (mapRingHom φ)).IsPrimitive)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+d*j ≤ w)
    (htop : ∃ j, F.coeff j ≠ 0 ∧ (F.coeff j).natDegree+d*j = w) :
    ((chart r w d F).map (mapRingHom φ)).IsPrimitive := by
  let ρ := algebraMap L (AlgebraicClosure L)
  intro b hb
  by_contra h
  have hdeg : (b.map ρ).degree ≠ 0 := by
    rw [degree_map_eq_of_injective ρ.injective]
    exact fun e => h (isUnit_iff_degree_eq_zero.mpr e)
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_root (b.map ρ) hdeg
  obtain ⟨j,hj⟩ := nonvanishing φ hφ F r w d hprim hW htop ρ a
  obtain ⟨q,hq⟩ := (C_dvd_iff_dvd_coeff _ _).mp hb j
  apply hj
  rw [Polynomial.coeff_map,coe_mapRingHom] at hq
  simp only [hq,Polynomial.map_mul,eval_mul,ha.eq_zero,zero_mul]

open SecondPrimeCoordinateWeight TerminalQuarticLocalization TerminalQuarticHessianTransport

/-- The actual coordinate weight of the input surface is attained in a nonzero
ordinate slot. This supplies the condition at chart coordinate zero. -/
theorem weight_profile (f : k[X][X][X]) (hf : f ≠ 0) (d : ℕ) :
    (∀ j, (orient f).coeff j ≠ 0 →
      ((orient f).coeff j).natDegree+d*j ≤ weight d f) ∧
    ∃ j, (orient f).coeff j ≠ 0 ∧
      ((orient f).coeff j).natDegree+d*j = weight d f := by
  classical
  have tc (j : ℕ) : (twist d f).coeff j = (orient f).coeff j * Polynomial.X^(d*j) := by
    rw [twist,comp_C_mul_X_coeff,←pow_mul]
    rfl
  have td (j : ℕ) (hn : (orient f).coeff j ≠ 0) :
      ((twist d f).coeff j).natDegree = ((orient f).coeff j).natDegree+d*j := by
    rw [tc,natDegree_mul hn (pow_ne_zero _ X_ne_zero),natDegree_X_pow]
  have ho : orient f ≠ 0 := by
    change permute f ≠ 0
    simpa only [map_zero] using permute.injective.ne hf
  have ht : twist d f ≠ 0 := by
    intro h
    have hj := leadingCoeff_ne_zero.mpr ho
    have hdv := mul_ne_zero hj (pow_ne_zero (d*(orient f).natDegree) (Polynomial.X_ne_zero (R:=k[X])))
    apply hdv
    change (orient f).coeff (orient f).natDegree * _ = 0
    rw [← tc, h,coeff_zero]
  refine ⟨fun j hn => (td j hn) ▸ Bivariate.coeff_natDegree_le_degreeX (twist d f) j,?_⟩
  obtain ⟨j,hj,he,_⟩ := Bivariate.exists_max_index_degreeX (twist d f) ht
  have hjn := mem_support_iff.mp hj
  have h : (orient f).coeff j ≠ 0 := fun h => hjn (by rw [tc,h,zero_mul])
  exact ⟨j,h,(td j h).symm.trans he⟩

/-- The transformed production cubic is primitive in the precise scalar-field
presentation of the two-polar site budget. -/
theorem primitive_of_original (f : k[X][X][X]) (hi : Irreducible f) (hy : 0 < f.natDegree)
    (r : k) (d : ℕ) :
    (localPlane (chart r (weight d f) d (orient f))).IsPrimitive := by
  obtain ⟨hw,ht⟩ := weight_profile f hi.ne_zero d
  have hp : (localPlane (orient f)).IsPrimitive := (local_generic (permute f)
    ((MulEquiv.irreducible_iff permute).mpr hi) (by rwa [permute_degree])).1
  exact primitive (algebraMap k[X] (RatFunc k)) (IsFractionRing.injective _ _)
    (orient f) r (weight d f) d hp hw ht

#print axioms primitive_of_original
#print axioms weight_profile
#print axioms nonvanishing
#print axioms primitive
end ArkLib.ProximityGap.Frontier.PrimitiveIntegralSectionChart
