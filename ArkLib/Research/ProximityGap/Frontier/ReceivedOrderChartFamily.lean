/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalChartReceivedOrder
import ArkLib.Research.ProximityGap.Frontier.IntegralSectionChart
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicPopulation

/-! # Original received multiplicities on the transformed production cubic

The finite set in the scalar function field is the injective image of the given
domain after the common reciprocal change. Its affine values remain linear in
the scalar and each new canonical order dominates the original one.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped Differential BigOperators
namespace ArkLib.ProximityGap.Frontier.ReceivedOrderChartFamily
open _root_.ProximityGap.CommonSectionChart IntegralSectionChart CanonicalQuarticSiteOrder
open IntrinsicCubicPopulation TruncatedJetMultipliers

variable {k I : Type} [Field k] [Fintype I]
local instance : Differential (RatFunc k) := scalarFieldDifferential k

private theorem constant_deriv (c : k) : (RatFunc.C c)′ = 0 := by
  let _ : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
  change (algebraMap k[X] (RatFunc k) (C c))′ = 0
  rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
  change algebraMap k[X] (RatFunc k) (C c).derivative = 0
  simp

private theorem parameter_deriv : (RatFunc.X : RatFunc k)′ = 1 := by
  let _ : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
  change (algebraMap k[X] (RatFunc k) Polynomial.X)′ = 1
  rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
  change algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]).derivative = 1
  simp

private theorem deriv_product {E : Type} [Field E] [Differential E] (a b : E) :
    (a*b)′ = a*b′+b*a′ := by simpa only [smul_eq_mul] using Differential.deriv.leibniz a b

private theorem affine_second (u v : k) :
    (RatFunc.C u+RatFunc.X*RatFunc.C v)′′ = 0 := by
  have h : (RatFunc.X*RatFunc.C v)′ = RatFunc.C v := by
    rw [deriv_product,constant_deriv,parameter_deriv,mul_zero,mul_one,zero_add]
  rw [map_add,constant_deriv,h,zero_add,constant_deriv]

/-- All original coordinates and received rows are carried into one actual chart.
The last conjunct is the literal site hypothesis of the descended cubic estimate. -/
theorem received_sites [Infinite k] (f : k[X][X][X]) (hf : f.natDegree≤3) (w d : ℕ)
    (hw : 3*d≤w) (hd : 1≤d)
    (hW : ∀ j, f.coeff j≠0 → Bivariate.degreeX (f.coeff j)+d*j≤w)
    (a : k) (dom : I ↪ k) (u v : I → k) (ha : ∀ i, dom i≠a)
    (hprim : ((chart a w d (orient f)).map (mapRingHom (algebraMap k[X] (RatFunc k)))).IsPrimitive) :
    let G := (chart a w d (orient f)).map (mapRingHom (algebraMap k[X] (RatFunc k)))
    ∃ (D : Finset (RatFunc k)) (l : RatFunc k → RatFunc k) (R : RatFunc k → ℕ),
      D.card = Fintype.card I ∧ (∑ i, originalOrder f (dom i) (u i) (v i)) ≤ (∑ z ∈ D, R z) ∧
      ∀ z ∈ D, z′ = 0 ∧ (l z)′′ = 0 ∧ ∃ j, Leader (ReceivedJetContact.shifted G z (l z)) (R z) j := by
  classical
  let _ : Infinite (RatFunc k) := Infinite.of_injective RatFunc.C RatFunc.C_injective
  let φ := algebraMap k[X] (RatFunc k)
  let F := (orient f).map (mapRingHom φ)
  let G := (chart a w d (orient f)).map (mapRingHom φ)
  let b (i : I) := (dom i-a)⁻¹
  let emb : I ↪ RatFunc k := ⟨fun i => RatFunc.C (b i),
    RatFunc.C_injective.comp (inv_injective.comp (sub_left_injective.comp dom.injective))⟩
  let w₀ (i : I) : RatFunc k := RatFunc.C (u i)+RatFunc.X*RatFunc.C (v i)
  let w₁ (i : I) : RatFunc k := RatFunc.C (b i^d*u i)+RatFunc.X*RatFunc.C (b i^d*v i)
  let l := Function.extend emb w₁ (fun _ => 0)
  let R (z : RatFunc k) := siteOrder G z (C (l z))
  have hl (i : I) : l (emb i) = w₁ i := emb.injective.extend_apply _ _ i
  have hw₁ (i : I) : w₁ i = emb i^d*w₀ i := by
    change RatFunc.C (_*_)+RatFunc.X*RatFunc.C (_*_) = (RatFunc.C _)^d*(_+_*_)
    simp only [map_mul,map_pow]
    ring
  have hdeg : F.natDegree≤3 := natDegree_map_le.trans (natDegree_map_le.trans hf)
  have gdeg : G.natDegree≤3 := natDegree_map_le.trans ((chart_natDegree a w d _).le.trans (natDegree_map_le.trans hf))
  have hslot (j : ℕ) (hn : F.coeff j ≠ 0) : (F.coeff j).natDegree+d*j ≤ w := by
    have hj : f.coeff j ≠ 0 := by intro hz; apply hn; simp [F,orient,hz]
    have bound : (F.coeff j).natDegree ≤ ((orient f).coeff j).natDegree := by
      simp only [F,coeff_map,coe_mapRingHom]
      exact natDegree_map_le
    exact (Nat.add_le_add_right bound _).trans (by rw [(orient_profile f j).1]; exact hW _ hj)
  have hG (j : ℕ) : G.coeff j = change (RatFunc.C a) (w-d*j) (F.coeff j) := by
    simp only [G,F,coeff_map,coe_mapRingHom,coeff_chart,← reflect_map,map_taylor,change]
    rfl
  have hOld (i : I) : originalOrder f (dom i) (u i) (v i) =
      siteOrder F (RatFunc.C (dom i)) (C (w₀ i)) := by
    unfold originalOrder IntrinsicReceivedSections.receivedOrder
    congr 1
    change C (φ (C (u i)+Polynomial.X*C (v i)))=_
    apply congrArg C
    rw [map_add,map_mul]
    rfl
  have each (i : I) : originalOrder f (dom i) (u i) (v i) ≤ R (emb i) ∧
      ∃ j, Leader (ReceivedJetContact.shifted G (emb i) (l (emb i))) (R (emb i)) j := by
    have hh := ReciprocalChartReceivedOrder.chart_site_leader (RatFunc.C a) (RatFunc.C (dom i))
      (w₀ i) (RatFunc.C_injective.ne (ha i)) w d hw hd F G hdeg gdeg hslot hG hprim
      _ (order_at_site F (RatFunc.C (dom i)) (C (w₀ i)))
    have hb : (RatFunc.C (dom i)-RatFunc.C a)⁻¹ = emb i := by
      change _ = RatFunc.C ((dom i-a)⁻¹)
      simp
    dsimp only at hh
    rw [hb,← hw₁] at hh
    simpa only [R,hl,hOld] using hh
  refine ⟨univ.map emb,l,R,by simp,?_,?_⟩
  · simpa only [sum_map,Function.Embedding.coeFn_mk] using
      (sum_le_sum (s := (univ : Finset I)) (fun i _ => (each i).1))
  · intro z hz
    obtain ⟨i,_,rfl⟩ := mem_map.mp hz
    exact ⟨constant_deriv _,by rw [hl]; exact affine_second _ _,(each i).2⟩

#print axioms received_sites
end ArkLib.ProximityGap.Frontier.ReceivedOrderChartFamily
