/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.TameCubicPowerSeries
import ArkLib.Research.ProximityGap.Frontier.TamePowerSeriesOrbit
import ArkLib.Research.ProximityGap.Frontier.BinaryBranchResultant
import ArkLib.Research.ProximityGap.Frontier.MonicRawPolynomialQuotient
import ArkLib.Research.ProximityGap.Frontier.PolynomialLocalOrder

/-! # The local projective formula for a primitive cubic

At every nonzero special fiber, a constant chart center makes the reciprocal
equation monic after scaling by a unit. The original padded resultant can then
be computed at all three projective sheets in the sixth-root parameter.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.ProjectiveCubicLocalOrder

open BinaryBranchResultant TamePowerSeriesOrbit TameCubicPowerSeries MonicRawPolynomialQuotient

variable {K : Type*} [Field K] [IsSepClosed K]

private theorem monic_three_coefficients {R : Type*} [CommRing R] [Nontrivial R] (f : R[X])
    (hf : f.Monic) (h : f.natDegree=3) :
    f = X^3+C (f.coeff 2)*X^2+C (f.coeff 1)*X+C (f.coeff 0) := by
  have h₃ : f.coeff 3 = 1 := by rw [← h]; exact hf
  calc
    f = ∑ i ∈ range 4, C (f.coeff i)*X^i := by simpa [h] using f.as_sum_range_C_mul_X_pow
    _ = _ := by simp [Finset.sum_range_succ, h₃]; ring

/-- Split the actual given monic cubic, retaining its polynomial identity. -/
theorem split_monic (f : K⟦X⟧[X]) (hf : f.Monic) (h : f.natDegree=3)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    ∃ y : Fin 3 → K⟦X⟧, f.map (PowerSeries.expand 6 (by decide) (R := K)).toRingHom =
      ∏ i, (X-C (y i)) := by
  obtain ⟨x,y,z,hs⟩ := monic_cubic_split (f.coeff 2) (f.coeff 1) (f.coeff 0) h₂ h₃
  refine ⟨![x,y,z],?_⟩
  conv_lhs => arg 2; rw [monic_three_coefficients f hf h]
  have happ (w : K⟦X⟧) : (PowerSeries.expand 6 (by decide) (R := K)).toRingHom w =
      PowerSeries.expand 6 (by decide) w := rfl
  simpa only [happ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero,
    mul_one, mul_assoc] using hs

/-- Cubic projective splitting over an arbitrary primitive special fiber.
The common unit is the discarded leading coefficient of the reciprocal
equation. Nonzero root coordinates are proved in the formal series ring. -/
theorem projective_split [Infinite K] (F : K⟦X⟧[X]) (hF : F.natDegree = 3)
    (hpr : F.map (PowerSeries.constantCoeff (R := K)) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    let e := (PowerSeries.expand 6 (by decide) (R := K)).toRingHom
    ∃ (c : K) (u : K⟦X⟧) (y : Fin 3 → K⟦X⟧), IsUnit u ∧ (∀ i, y i ≠ 0) ∧
      F.map e = C u*∏ i, (C (-y i)*X-C (-(1+PowerSeries.C c*y i))) := by
  classical
  let φ := (PowerSeries.expand 6 (by decide) (R := K)).toRingHom
  let f := F.map (PowerSeries.constantCoeff (R := K))
  obtain ⟨c,hc⟩ := Infinite.exists_notMem_finset f.roots.toFinset
  have hc₀ : f.eval c ≠ 0 := fun h => hc (Multiset.mem_toFinset.mpr ((mem_roots hpr).mpr h))
  have hunit : IsUnit (F.eval (PowerSeries.C c)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    have hv : (F.map PowerSeries.constantCoeff).eval (PowerSeries.constantCoeff (PowerSeries.C c)) =
        PowerSeries.constantCoeff (F.eval (PowerSeries.C c)) := by rw [eval_map, eval₂_hom]
    rw [PowerSeries.constantCoeff_C] at hv
    exact fun H => hc₀ (hv.trans H)
  let T := (F.taylor (PowerSeries.C c)).reflect 3
  obtain ⟨hT,hU⟩ := reciprocal_chart_leading_unit F (PowerSeries.C c) 3 hF.le hunit
  obtain ⟨v,hv⟩ := hU
  change (v : K⟦X⟧) = T.leadingCoeff at hv
  let Q := C (↑v⁻¹ : K⟦X⟧)*T
  have hQ : Q.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [← hv])
  have hQd : Q.natDegree = 3 := by
    rw [show Q = _ from rfl, natDegree_C_mul (Units.ne_zero _)]
    exact hT
  obtain ⟨y,hy⟩ := split_monic Q hQ hQd h₂ h₃
  have hTQ : T = C (v : K⟦X⟧)*Q := by simp [Q, ← mul_assoc, ← map_mul]
  have hTy : T.map φ = C (φ v)*∏ i, (X-C (y i)) := by
    rw [hTQ, Polynomial.map_mul, map_C]
    exact congrArg (C (φ v) * ·) hy
  have h0 : T.coeff 0 ≠ 0 := by
    dsimp [T]
    rw [coeff_reflect, revAt_zero]
    have ht : (F.taylor (PowerSeries.C c)).natDegree = 3 := (natDegree_taylor _ _).trans hF
    rw [← ht]
    apply leadingCoeff_ne_zero.mpr
    intro hz
    simp [hz] at ht
  have h0φ : (T.map φ).eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact fun H => h0 (expand_injective (by decide : 6≠0) (H.trans (map_zero φ).symm))
  have hy0 (i : Fin 3) : y i ≠ 0 := by
    intro hz
    apply h0φ
    rw [hTy, eval_mul, eval_prod, Finset.prod_eq_zero (mem_univ i) (by simp [hz]), mul_zero]
  have hfull : ((F.map φ).taylor (PowerSeries.C c)).reflect (Fintype.card (Fin 3)) =
      C (φ v)*∏ i, (X-C (y i)) := by
    have hC : φ (PowerSeries.C c) = PowerSeries.C c := PowerSeries.expand_C _ _ _
    simpa only [T, ← Polynomial.reflect_map, Polynomial.map_taylor, hC, Fintype.card_fin] using hTy
  exact ⟨c,φ v,y,v.isUnit.map φ,hy0,recover_original _ _ _ _ hfull⟩

/-- The local padded resultant order of the original primitive cubic is
the sum of projective sheet orders in the sixth-root parameter, divided by six.
The same three unimodular coordinate pairs work for every test polynomial. -/
theorem projective_resultant_orders [Infinite K] (F : K⟦X⟧[X]) (hF : F.natDegree = 3)
    (hpr : F.map (PowerSeries.constantCoeff (R := K)) ≠ 0)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    let e := (PowerSeries.expand 6 (by decide) (R := K)).toRingHom
    ∃ (c : K) (u : K⟦X⟧) (y : Fin 3 → K⟦X⟧), IsUnit u ∧ (∀ i, y i ≠ 0) ∧
      (∀ i, IsCoprime (-(1+PowerSeries.C c*y i)) (-y i)) ∧
      F.map e = C u*∏ i, (C (-y i)*X-C (-(1+PowerSeries.C c*y i))) ∧
      ∀ (G : K⟦X⟧[X]) (h : ℕ), G.natDegree ≤ h →
        6 • (F.resultant G 3 h).order =
          ∑ i, (binaryValue (G.map e) h (-(1+PowerSeries.C c*y i)) (-y i)).order := by
  classical
  let e := (PowerSeries.expand 6 (by decide) (R := K)).toRingHom
  obtain ⟨c,u,y,hu,hy,hfactor⟩ := projective_split F hF hpr h₂ h₃
  refine ⟨c,u,y,hu,hy,fun i => ⟨-1,PowerSeries.C c,by ring⟩,hfactor,?_⟩
  intro G h hG
  have hg := (Polynomial.natDegree_map_le (p := G) (f := e)).trans hG
  have hval : e (F.resultant G 3 h) = u^h*∏ i,
      binaryValue (G.map e) h (-(1+PowerSeries.C c*y i)) (-y i) := by
    rw [← resultant_map_map F G 3 h e, show F.map e = _ from hfactor]
    exact product_resultant _ _ (fun i => neg_ne_zero.mpr (hy i)) (G.map e) h hg u
  have ho := congrArg PowerSeries.order hval
  have hu' : u.order = 0 := by
    by_contra! hn
    exact (PowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hn)
  change (PowerSeries.expand 6 (by decide) (F.resultant G 3 h)).order = _ at ho
  simpa only [PowerSeries.order_expand, PowerSeries.order_mul, PowerSeries.order_pow, hu',
    nsmul_zero, zero_add, PowerSeries.order_prod] using ho

/-- Starting on the polynomial X-line itself, the three common chart
sheets compute the root multiplicity of every nonzero padded resultant. -/
theorem polynomial_projective_orders [Infinite K] (F : K[X][X]) (hF : F.natDegree = 3)
    (hprim : F.IsPrimitive) (x₀ : K) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) :
    let θ := PolynomialLocalOrder.atPoint x₀
    let e := (PowerSeries.expand 6 (by decide) (R := K)).toRingHom
    ∃ (c : K) (u : K⟦X⟧) (y : Fin 3 → K⟦X⟧), IsUnit u ∧ (∀ i, y i ≠ 0) ∧
      (∀ i, IsCoprime (-(1+PowerSeries.C c*y i)) (-y i)) ∧
      (F.map θ).map e = C u*∏ i, (C (-y i)*X-C (-(1+PowerSeries.C c*y i))) ∧
      ∀ (G : K[X][X]) (h : ℕ), G.natDegree ≤ h → F.resultant G 3 h ≠ 0 →
        6 • ((F.resultant G 3 h).rootMultiplicity x₀ : ℕ∞) =
          ∑ i, (binaryValue ((G.map θ).map e) h (-(1+PowerSeries.C c*y i)) (-y i)).order := by
  let θ := PolynomialLocalOrder.atPoint x₀
  have hd : (F.map θ).natDegree=3 :=
    (natDegree_map_eq_of_injective (PolynomialLocalOrder.atPoint_injective x₀) F).trans hF
  have hpr : (F.map θ).map (PowerSeries.constantCoeff (R := K)) ≠ 0 := by
    rw [Polynomial.map_map]
    exact PolynomialLocalOrder.primitive_map_ne_zero F hprim _
  obtain ⟨c,u,y,hu,hy,hco,hfactor,hres⟩ := projective_resultant_orders (F.map θ) hd hpr h₂ h₃
  refine ⟨c,u,y,hu,hy,hco,hfactor,?_⟩
  intro G h hG hr
  have ht := hres (G.map θ) h (natDegree_map_le.trans hG)
  rw [resultant_map_map, PolynomialLocalOrder.local_order x₀ _ hr] at ht
  exact ht

omit [IsSepClosed K] in
/-- The nominal second equation 1 of degree one is the hyperplane at infinity.
On the three sheets this gives exactly the orders of their denominators. -/
theorem pole_order_of_tests (F : K[X][X]) (hF : F.natDegree = 3) (α c : K)
    (y : Fin 3 → K⟦X⟧)
    (hord : ∀ (G : K[X][X]) (h : ℕ), G.natDegree ≤ h → F.resultant G 3 h ≠ 0 →
      6 • ((F.resultant G 3 h).rootMultiplicity α : ℕ∞) = ∑ i,
        (binaryValue ((G.map (PolynomialLocalOrder.atPoint α)).map
          (PowerSeries.expand 6 (by decide) (R := K)).toRingHom)
          h (-(1+PowerSeries.C c*y i)) (-y i)).order) :
    ∑ i, (y i).order = 6 • (F.leadingCoeff.rootMultiplicity α : ℕ∞) := by
  have he : F.resultant 1 3 1 = F.leadingCoeff := by
    rw [resultant_one_right, pow_one, ← hF]
    rfl
  have hne : F.resultant 1 3 1 ≠ 0 := he ▸ leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hF)
  have hh := hord 1 1 (by simp) hne
  have hbin (x z : K⟦X⟧) : binaryValue (1 : K⟦X⟧[X]) 1 x z = z := by
    have hs : (1 : K⟦X⟧[X]).support = {0} := by
      simpa only [map_one] using (support_C (one_ne_zero (α := K⟦X⟧)))
    simp [binaryValue, Polynomial.sum, hs]
  simpa only [he, Polynomial.map_one, hbin, PowerSeries.order_neg] using hh.symm

omit [IsSepClosed K] in
/-- Local pole sums over any finite set cost at most six times the coordinate
degree of the leading value coefficient. -/
theorem sum_poles_le (f : K[X]) (hf : f ≠ 0) (s : Finset K)
    (y : K → Fin 3 → K⟦X⟧)
    (hp : ∀ α ∈ s, ∑ i, (y α i).order = 6 • (f.rootMultiplicity α : ℕ∞)) :
    ∑ α ∈ s, ∑ i, (y α i).order ≤ 6 • (f.natDegree : ℕ∞) := by
  classical
  rw [sum_congr rfl hp]
  have H := PolynomialLocalOrder.sum_local_orders_le f hf s
  simp only [PolynomialLocalOrder.local_order _ f hf, ENat.toNat_natCast] at H
  have H' : (∑ α ∈ s, (f.rootMultiplicity α : ℕ∞)) ≤ (f.natDegree : ℕ∞) := by exact_mod_cast H
  rw [← Finset.smul_sum]
  exact nsmul_le_nsmul_right H' 6

#print axioms sum_poles_le
#print axioms pole_order_of_tests
#print axioms polynomial_projective_orders
#print axioms projective_resultant_orders
#print axioms split_monic
#print axioms projective_split

end ArkLib.ProximityGap.Frontier.ProjectiveCubicLocalOrder
