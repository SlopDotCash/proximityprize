/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.IntrinsicReceivedSections

/-! # Weighted reverse-Hessian charge at the original received sites -/

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Bivariate Finset ArkLib.BivariateDegreeToolkit
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.ReceivedHessianCharge
open ScalarHessianLocalOrder WeightedHessianResultant CanonicalQuarticSiteOrder
open SylvesterLocalMultiplicity

/-- The padded value resultant charges every original site by the product of its
two joint orders, including coordinate fibers where either degree drops. -/
theorem site_charge {K E : Type} [Field K] [Field E] [Differential K[X]]
    (φ : K[X] →+* E) (hi : Function.Injective φ) (F : K[X][X])
    (b d W : ℕ) (hb₂ : 2 ≤ b) (hf : F.natDegree = b)
    (hir : Irreducible (F.map φ)) (hnd : ¬F.map φ ∣ (hessian F).map φ)
    (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree) (hW : b*d ≤ W)
    (hw : natWeightedDegree F 1 d ≤ W)
    (S : Finset K) (w : K → K[X]) (hπ : ∀ a ∈ S, (Polynomial.X-C a : K[X])′ = 0)
    (hl : ∀ a ∈ S, ((w a)′)′ = 0) :
    (∑ a ∈ S, let r := siteOrder F a (w a); r*(3*r-2)) + 3*b^2*d ≤ (6*b-2)*W := by
  have hv : 2*d ≤ W := (Nat.mul_le_mul_right d hb₂).trans hW
  have hH := hessian_weight hD F 1 d W hv hw
  have hY : (hessian F).natDegree ≤ 3*b-2 := by
    change natDegreeY (hessian F) ≤ _
    rw [degreeY_as_weighted_deg]
    have hy : natDegreeY F ≤ b := hf.le
    rw [degreeY_as_weighted_deg] at hy
    exact hessian_weight hD F 0 1 b (by omega) hy
  have hc (g : K[X][X]) (v : ℕ) (hg : natWeightedDegree g 1 d ≤ v)
      (j : ℕ) (hj : g.coeff j ≠ 0) : (g.coeff j).natDegree+d*j ≤ v := by
    simpa using (weight_coeff_le_natWeightedDegree g 1 d (mem_support_iff.mpr hj)).trans hg
  have hdeg := weighted_resultant_le F (hessian F) b (3*b-2) d W (3*W-2*d)
    (hc F W hw) (hc _ _ hH)
  have hn := padded_ne_zero φ hi F (hessian F) (3*b-2) hY hir hnd
  let r (a : K) := siteOrder F a (w a)
  have hs := sum_local_orders_le_natDegree _ hn S (fun a => r a*(3*r a-2)) (by
    intro a ha
    have hr : r a ≤ F.natDegree  := siteOrder_le ..
    have ho := order_at_site F a (w a)
    exact pow_dvd_resultant_of_taylor _ _ _ _ hr (by omega) hY ho
      (translated_hessian_order (hπ a ha) (hl a ha) ho))
  rw [hf] at hs
  have hsum := hs.trans hdeg
  change (∑ a ∈ S, r a*(3*r a-2)) + 3*b^2*d ≤ (6*b-2)*W
  let N := 3*b-2
  let H := 3*W-2*d
  have hN : N+2 = 3*b := by dsimp [N]; omega
  have hH : H+2*d = 3*W := by dsimp [H]; omega
  have hNW : b*N*d ≤ N*W := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left N hW
  have hpad : b*N*d ≤ N*W+b*H := hNW.trans (Nat.le_add_right ..)
  change _ ≤ N*W+b*H-b*N*d at hsum
  have hlin := Nat.add_le_add_right hsum (b*N*d)
  rw [Nat.sub_add_cancel hpad] at hlin
  have hid : 3*b^2*d = b*N*d + 2*b*d := calc
    _ = b*(3*b)*d := by ring
    _ = b*(N+2)*d := by rw [hN]
    _ = _ := by ring
  rw [hid,← Nat.add_assoc]
  calc
    _ ≤ N*W+b*H+2*b*d := Nat.add_le_add_right hlin _
    _ = N*W+b*(H+2*d) := by ring
    _ = (N+3*b)*W := by rw [hH]; ring
    _ = _ := by rw [show N+3*b=6*b-2 by omega]

private theorem deriv_product {E : Type*} [Field E] [Differential E] (a b : E) :
    (a*b)′ = a*b′+b*a′ := by simpa only [smul_eq_mul] using Differential.deriv.leibniz a b


/-- The charged sites are precisely the received affine lines over the rational scalar
field. All local differentiation and specialization hypotheses are discharged. -/
theorem received_charge {k : Type} [Field k] (F : (RatFunc k)[X][X])
    (b d W : ℕ) (hb₂ : 2 ≤ b) (hf : F.natDegree = b)
    (hir : Irreducible (MovingCubicVanishingBranch.genericEquation F))
    (hnd : ¬MovingCubicVanishingBranch.genericEquation F ∣
      MovingCubicVanishingBranch.genericEquation (scalarFieldHessian F))
    (hW : b*d ≤ W) (hw : natWeightedDegree F 1 d ≤ W)
    (D : Finset k) (u v : k → k) :
    (∑ a ∈ D, let r := siteOrder F (RatFunc.C a) (C (RatFunc.C (u a)+RatFunc.X*RatFunc.C (v a)));
      r*(3*r-2)) + 3*b^2*d ≤ (6*b-2)*W := by
  classical
  let _ : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
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
  let emb : k ↪ RatFunc k := ⟨RatFunc.C, RatFunc.C_injective⟩
  let recover (z : RatFunc k) := z.num.coeff 0
  let line (z : RatFunc k) : RatFunc k := RatFunc.C (u (recover z))+
    RatFunc.X*RatFunc.C (v (recover z))
  have hline (z : RatFunc k) : (line z)′ = RatFunc.C (v (recover z)) := by
    dsimp only [line]
    rw [map_add, hC, deriv_product, hC, hZ]
    simp

  have hbound := site_charge (algebraMap _ (RatFunc (RatFunc k))) (RatFunc.algebraMap_injective _)
    F b d W hb₂ hf hir hnd ImplicitDerivativeBidegree.coefficientDifferential_degree hW hw
    (D.map emb) (fun z => C (line z)) (by
      intro z hz
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hz
      change Differential.mapCoeffs (Polynomial.X-C (RatFunc.C a)) = 0
      simp [hC]) (by
      intro z _
      change Differential.mapCoeffs (Differential.mapCoeffs (C (line z))) = 0
      simp only [Differential.mapCoeffs_C, hline, hC, map_zero])
  simpa [emb,line,recover] using hbound

#print axioms site_charge
#print axioms received_charge
end ArkLib.ProximityGap.Frontier.ReceivedHessianCharge
