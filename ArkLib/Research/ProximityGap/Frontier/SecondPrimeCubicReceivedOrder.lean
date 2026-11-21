/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart

/-! # A proper cubic's Hessian bound at its actual affine received rows

At a site of joint order r, the translated Hessian has order at least 3r−2.
The padded degree-seven Sylvester resultant thus vanishes to order r(3r−2).
This gives a received-site bound depending only on the cubic's own weight.
-/

open Polynomial Polynomial.Bivariate Finset ArkLib.BivariateDegreeToolkit
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicReceivedOrder

open ScalarHessianLocalOrder WeightedHessianResultant CanonicalQuarticSiteOrder
open SecondPrimeScalarChart SecondPrimeCoordinateWeight MovingCubicVanishingBranch

private theorem degree_bounds {k : Type} [Field k] [Differential k[X]]
    (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree) (f : k[X][X]) (d W : ℕ)
    (hd : f.natDegree = 3) (hw : natWeightedDegree f 1 d ≤ W) :
    (hessian f).natDegree ≤ 7 ∧ (resultant f (hessian f) 3 7).natDegree + 27*d ≤ 16*W := by
  have hcoeff (g : k[X][X]) (b : ℕ) (hg : natWeightedDegree g 1 d ≤ b)
      (j : ℕ) (hj : g.coeff j ≠ 0) : (g.coeff j).natDegree + d*j ≤ b := by
    simpa using (weight_coeff_le_natWeightedDegree g 1 d (mem_support_iff.mpr hj)).trans hg
  have hne : f ≠ 0 := by intro hz; simp [hz] at hd
  have hh := hcoeff f W hw f.natDegree (leadingCoeff_ne_zero.mpr hne)
  rw [hd] at hh
  have hH := hessian_weight hD f 1 d W (by omega) hw
  constructor
  · change natDegreeY (hessian f) ≤ 7
    rw [degreeY_as_weighted_deg]
    change natDegreeY f = 3 at hd
    rw [degreeY_as_weighted_deg] at hd
    exact hessian_weight hD f 0 1 3 (by decide) hd.le
  · have h := weighted_resultant_le f (hessian f) 3 7 d W (3*W-2*d)
      (hcoeff f W hw) (hcoeff _ _ hH)
    omega

private theorem canonical {k E : Type} [Field k] [Differential k[X]] [Field E]
    (φ : k[X] →+* E) (hinj : Function.Injective φ) (F : k[X][X])
    (hir : Irreducible (F.map φ)) (hnd : ¬ F.map φ ∣ (hessian F).map φ)
    (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree) (d W : ℕ) (hd : F.natDegree = 3)
    (hw : natWeightedDegree F 1 d ≤ W) (S : Finset k) (w : k → k[X])
    (hπ : ∀ a ∈ S, (Polynomial.X - C a : k[X])′ = 0) (hl : ∀ a ∈ S, (w a)′′ = 0) :
    7 * (∑ a ∈ S, siteOrder F a (w a)) + 27*d ≤ 6*S.card + 16*W := by
  obtain ⟨hH, hdeg⟩ := degree_bounds hD F d W hd hw
  have hR := padded_ne_zero φ hinj F (hessian F) 7 hH hir hnd
  rw [hd] at hR
  let r (a : k) := siteOrder F a (w a)
  have hr (a : k) : r a ≤ 3 := (siteOrder_le F a (w a)).trans hd.le
  have hs := SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hR S
    (fun a => r a*(3*r a-2)) (by
      intro a ha
      conv_rhs => rw [← hd]
      exact SylvesterLocalMultiplicity.pow_dvd_resultant_of_taylor (r := r a) (s := 3*r a-2)
        (n := 7) (Polynomial.X-C a) (w a) F (hessian F)
        (siteOrder_le F a (w a)) (by have := hr a; omega) hH (order_at_site F a (w a))
        (translated_hessian_order (hπ a ha) (hl a ha) (order_at_site F a (w a))))
  have hlin : ∀ a ∈ S, 7*r a ≤ 6 + r a*(3*r a-2) := by
    intro a _
    have hh := hr a
    interval_cases h : r a <;> decide
  have hsum := Finset.sum_le_sum hlin
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  change 7 * (∑ a ∈ S, r a) + 27*d ≤ 6*S.card + 16*W
  omega

/-- The actual scalar-rational cubic receives this sum bound for every injectively
presented evaluation domain and its two original received rows. -/
theorem received_budget {k I : Type} [Field k] [Fintype I] (F : (RatFunc k)[X][X])
    (d W : ℕ) (hcubic : F.natDegree = 3) (hir : Irreducible (genericEquation F))
    (hnd : ¬ genericEquation F ∣ genericEquation (scalarFieldHessian F))
    (hw : natWeightedDegree F 1 d ≤ W) (dom : I ↪ k) (u v : I → k) :
    7 * (∑ i, siteOrder F (RatFunc.C (dom i)) (C (RatFunc.C (u i) + RatFunc.X * RatFunc.C (v i))))
      + 27*d ≤ 6*Fintype.card I + 16*W := by
  classical
  let _ : Differential k[X] := coordinateDifferential
  let _ : Differential (RatFunc k) := scalarFieldDifferential k
  let _ : Differential (RatFunc k)[X] := ImplicitDerivativeBidegree.coefficientDifferential
  have hC (a : k) : (RatFunc.C a)′ = 0 := by
    change (algebraMap k[X] (RatFunc k) (C a))′ = 0
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (C a).derivative = 0
    simp
  have hZ : (RatFunc.X : RatFunc k)′ = 1 := by
    change (algebraMap k[X] (RatFunc k) Polynomial.X)′ = 1
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]).derivative = 1
    simp
  let e := dom.trans (⟨RatFunc.C, RatFunc.C_injective⟩ : k ↪ RatFunc k)
  let w (i : I) := C (RatFunc.C (u i) + RatFunc.X * RatFunc.C (v i))
  let W' := Function.extend e w (fun _ => 0)
  have he (i : I) : W' (e i) = w i := e.injective.extend_apply _ _ i
  have bound := canonical (algebraMap _ (RatFunc (RatFunc k))) (RatFunc.algebraMap_injective _)
    F hir hnd ImplicitDerivativeBidegree.coefficientDifferential_degree d W hcubic hw
    (univ.map e) W' (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_map.mp hz
      change Differential.mapCoeffs (Polynomial.X-C (RatFunc.C (dom i))) = 0
      simp [hC]) (by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_map.mp hz
      rw [he]
      change Differential.mapCoeffs (Differential.mapCoeffs (C _)) = 0
      simp [hC, hZ])
  simp only [sum_map, card_map, card_univ, he] at bound
  exact bound

/-- The raw factor's coordinate weight gives the same bound on its actual chart. -/
theorem actual_received_budget {K I : Type} [Field K] [Fintype I] (f : Surface K)
    (hi : Irreducible f) (hc : f.natDegree = 3) (dom : I ↪ K) (u v : I → K) (d : ℕ)
    (hnd : ¬ genericEquation (scalarChart f) ∣
      genericEquation (scalarFieldHessian (scalarChart f))) :
    7 * (∑ i, siteOrder (scalarChart f) (RatFunc.C (dom i))
      (C (RatFunc.C (u i) + RatFunc.X * RatFunc.C (v i)))) + 27*d ≤
        6*Fintype.card I + 16*weight d f :=
  received_budget (scalarChart f) d (weight d f) ((value_degree f).trans hc)
    (generic_irreducible f hi (by omega)) hnd (chart_weight f d) dom u v

#print axioms actual_received_budget
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicReceivedOrder
