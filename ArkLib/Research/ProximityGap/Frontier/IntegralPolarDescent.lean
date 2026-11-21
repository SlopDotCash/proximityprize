/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.IntegralOrdinaryPolars
import ArkLib.Research.ProximityGap.Frontier.CubicPolarDescent
import ArkLib.Research.ProximityGap.Frontier.GenericProjectivePolarGcd
import ArkLib.Research.ProximityGap.Frontier.ReceivedPolarContacts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # Ordinary polars over the rational function field of the scalar variable -/

noncomputable section
open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.IntegralPolarDescent

variable {k K : Type} [Field k] [Field K]

/-- Pass the scalar coefficients to their rational function field. -/
def generic (C₀ : k[X][X][X]) : (RatFunc k)[X][X] :=
  C₀.map (mapRingHom (algebraMap k[X] (RatFunc k)))

/-- The generic polar is the image of the integral polar, with the same constant slope. -/
theorem resultant_eq (C₀ : k[X][X][X]) (c : k) :
    (IntegralOrdinaryPolars.polarResultant C₀ (C c)).map (algebraMap k[X] (RatFunc k)) =
      (generic C₀).resultant (GenericProjectivePolarGcd.polar (ReceivedPolarContacts.dx (generic C₀))
        (generic C₀).derivative (algebraMap k (RatFunc k) c)) 3 3 := by
  have eqc : algebraMap k[X] (RatFunc k) (C c) = algebraMap k (RatFunc k) c :=
    (IsScalarTower.algebraMap_apply k k[X] (RatFunc k) c).symm
  rw [IntegralOrdinaryPolars.map_resultant, eqc]
  rfl

private theorem gcd_degree_map_le {L : Type} [Field L] [DecidableEq K] [DecidableEq L]
    (φ : K →+* L) (A B : K[X]) :
    (GCDMonoid.gcd A B).natDegree ≤ (GCDMonoid.gcd (A.map φ) (B.map φ)).natDegree := by
  by_cases hz : GCDMonoid.gcd (A.map φ) (B.map φ) = 0
  · have hA := gcd_dvd_left (A.map φ) (B.map φ)
    have hB := gcd_dvd_right (A.map φ) (B.map φ)
    rw [hz, zero_dvd_iff] at hA hB
    have hAz := (Polynomial.map_injective φ φ.injective) (hA.trans (Polynomial.map_zero φ).symm)
    have hBz := (Polynomial.map_injective φ φ.injective) (hB.trans (Polynomial.map_zero φ).symm)
    simp [hAz, hBz]
  have hd := dvd_gcd (Polynomial.map_dvd φ (gcd_dvd_left A B))
    (Polynomial.map_dvd φ (gcd_dvd_right A B))
  simpa only [natDegree_map_eq_of_injective φ.injective] using natDegree_le_of_dvd hd hz

set_option maxHeartbeats 1500000 in
private theorem degree_equiv {L : Type} [Field L] [DecidableEq K] [DecidableEq L]
    (φ : K ≃+* L) (A B : K[X]) :
    (GCDMonoid.gcd A B).natDegree = (GCDMonoid.gcd (A.map φ.toRingHom) (B.map φ.toRingHom)).natDegree := by
  have hback (T : K[X]) : (T.map φ.toRingHom).map φ.symm.toRingHom = T := by
    ext j
    simp only [coeff_map]
    exact φ.symm_apply_apply _
  have rev := gcd_degree_map_le φ.symm.toRingHom (A.map φ.toRingHom) (B.map φ.toRingHom)
  rw [hback A, hback B] at rev
  exact le_antisymm (gcd_degree_map_le φ.toRingHom A B) rev

/-- The chart's integral gcd degree is the actual polynomial gcd degree over RatFunc. -/
theorem genericDegree_eq [DecidableEq (RatFunc k)] (A B : k[X][X]) :
    OrdinaryPolarGcdBudget.genericDegree A B =
      (GCDMonoid.gcd (A.map (algebraMap k[X] (RatFunc k)))
        (B.map (algebraMap k[X] (RatFunc k)))).natDegree := by
  classical
  let φ := FractionRing.algEquiv k[X] (RatFunc k)
  let m := algebraMap k[X] (FractionRing k[X])
  have hcomp : φ.toRingEquiv.toRingHom.comp m = algebraMap k[X] (RatFunc k) :=
    RingHom.ext φ.commutes
  change (GCDMonoid.gcd (A.map m) (B.map m)).natDegree = _
  simpa only [Polynomial.map_map, hcomp] using degree_equiv φ.toRingEquiv (A.map m) (B.map m)

/-- A nonzero value-derivative resultant admits an ordinary polar of nonzero resultant.
Its slope can be chosen in the specified infinite field of constants. -/
theorem exists_first [Infinite k] (ι : k →+* K) (F : K[X][X]) (hf : F.natDegree = 3)
    (hprim : F.IsPrimitive) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hV : F.resultant F.derivative 3 3 ≠ 0) (except : Finset k) :
    ∃ c ∉ except, F.resultant (GenericProjectivePolarGcd.polar (ReceivedPolarContacts.dx F)
      F.derivative (ι c)) 3 3 ≠ 0 := by
  classical
  let L := SeparableClosure K
  let φ := algebraMap K L
  let : Infinite L := Infinite.of_injective (φ.comp ι) (φ.comp ι).injective
  let m := mapRingHom φ
  let G := F.map m
  have hm : Function.Injective m := Polynomial.map_injective _ φ.injective
  have hg : G.natDegree = 3 := (natDegree_map_eq_of_injective hm _).trans hf
  have gp : G.IsPrimitive := by
    apply isPrimitive_of_contentIdeal_eq_top
    rw [show G = F.map m from rfl, contentIdeal_map_eq_map_contentIdeal,
      (isPrimitive_iff_contentIdeal_eq_top F).mp hprim, Ideal.map_top]
  have h2 : (2 : L) ≠ 0 := fun he => h₂ (φ.injective (by simpa only [map_ofNat, map_zero] using he))
  have h3 : (3 : L) ≠ 0 := fun he => h₃ (φ.injective (by simpa only [map_ofNat, map_zero] using he))
  obtain ⟨t, u, y, hcharts, _⟩ := GenericProjectivePolarGcd.primitive_norm_charts G hg gp h2 h3
  have hG : G.resultant G.derivative 3 3 ≠ 0 := by
    change (F.map m).resultant (F.map m).derivative 3 3 ≠ 0
    rw [derivative_map, resultant_map_map]
    exact fun he => hV ((Polynomial.map_injective _ φ.injective)
      (he.trans (Polynomial.map_zero φ).symm))
  have hdx : (ReceivedPolarContacts.dx G).natDegree ≤ 3 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [ReceivedPolarContacts.coeff_dx, coeff_eq_zero_of_natDegree_lt (hg.trans_lt hj),
      derivative_zero]
  obtain ⟨c, hc, hR, _⟩ := GenericProjectivePolarGcd.generic_second_polar (φ.comp ι) G
    (ReceivedPolarContacts.dx G) G.derivative 3 hdx ((natDegree_derivative_le _).trans (by omega))
    hG _ _ hcharts ∅ except
  refine ⟨c,hc,fun he => hR ?_⟩
  have map_res := IntegralOrdinaryPolars.map_resultant φ F (ι c)
  change IntegralOrdinaryPolars.polarResultant F (ι c) = 0 at he
  change IntegralOrdinaryPolars.polarResultant G (φ (ι c)) = 0
  rw [← map_res, he, Polynomial.map_zero]

/-- The weighted chart bounds the degree of the first polar in the same generic field. -/
theorem bounded_first [Infinite k] (C₀ : k[X][X][X]) (w d p : ℕ) (hd : 1 ≤ d) (hw : 1 ≤ w)
    (hW : ∀ j, C₀.coeff j ≠ 0 → (C₀.coeff j).natDegree + d*j ≤ w)
    (hsmall : 6*w-9*d-3 < p) (hf : (generic C₀).natDegree = 3)
    (hprim : (generic C₀).IsPrimitive) (h₂ : (2 : RatFunc k) ≠ 0) (h₃ : (3 : RatFunc k) ≠ 0)
    (hV : (generic C₀).resultant (generic C₀).derivative 3 3 ≠ 0) (except : Finset k) :
    ∃ c ∉ except, let A := IntegralOrdinaryPolars.polarResultant C₀ (C c)
      A ≠ 0 ∧ A.map (algebraMap k[X] (RatFunc k)) ≠ 0 ∧
        (A.map (algebraMap k[X] (RatFunc k))).natDegree < p := by
  obtain ⟨c, hc, hR⟩ := exists_first (algebraMap k (RatFunc k)) (generic C₀) hf hprim h₂ h₃ hV except
  rw [← resultant_eq] at hR
  refine ⟨c,hc,fun hz => hR (by rw [hz,Polynomial.map_zero]),hR,?_⟩
  exact (natDegree_map_le.trans (IntegralOrdinaryPolars.coordinate_bound _ _ d w hd hw hW)).trans_lt hsmall

open scoped Differential
local instance [Differential (RatFunc k)] : Differential (RatFunc k)[X] := ⟨Differential.mapCoeffs⟩

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
/-- Lower bounds on the gcd for all nonzero integral polar pairs imply the absolute
received-site order bound on the rational-function cubic. -/
theorem order_budget_of_defect [Infinite k] [Differential (RatFunc k)]
    (C₀ : k[X][X][X]) (w p defect : ℕ) [CharP (RatFunc k) p]
    (hw : 201326589 ≤ w) (hp : 6*w-9*67108863-3 < p)
    (hW : ∀ j, C₀.coeff j ≠ 0 → (C₀.coeff j).natDegree + 67108863*j ≤ w)
    (hf : (generic C₀).natDegree = 3) (hprim : (generic C₀).IsPrimitive)
    (h₂ : (2 : RatFunc k) ≠ 0) (h₃ : (3 : RatFunc k) ≠ 0)
    (hV : (generic C₀).resultant (generic C₀).derivative 3 3 ≠ 0)
    (hH : (generic C₀).resultant (ScalarHessianLocalOrder.hessian (generic C₀)) 3 7 ≠ 0)
    (hpolar : ∀ c₁ c₂ : k, IntegralOrdinaryPolars.polarResultant C₀ (C c₁) ≠ 0 →
      IntegralOrdinaryPolars.polarResultant C₀ (C c₂) ≠ 0 →
      2*(w-67108863) ≤ OrdinaryPolarGcdBudget.genericDegree
        (IntegralOrdinaryPolars.polarResultant C₀ (C c₁))
        (IntegralOrdinaryPolars.polarResultant C₀ (C c₂)) + defect)
    (D : Finset (RatFunc k)) (l : RatFunc k → RatFunc k) (r : RatFunc k → ℕ)
    (hsite : ∀ α ∈ D, α′ = 0 ∧ (l α)′′ = 0 ∧ ∃ i, TruncatedJetMultipliers.Leader
      (ReceivedJetContact.shifted (generic C₀) α (l α)) (r α) i) :
    3*(∑ α ∈ D, r α) + 35*67108863 ≤ 2*D.card + 16*w + 2*defect := by
  classical
  obtain ⟨c, _, hcr, hA, hAp⟩ := bounded_first C₀ w 67108863 p (by decide) (by omega)
    hW hp hf hprim h₂ h₃ hV ∅
  let m := algebraMap k[X] (RatFunc k)
  let A := (IntegralOrdinaryPolars.polarResultant C₀ (C c)).map m
  obtain ⟨b, _, hB, hbudget⟩ := CubicPolarDescent.cubic_site_budget
    (algebraMap k (RatFunc k)) p h₂ h₃ (generic C₀) hf hprim hV hH A hA hAp {c} D l r hsite
  let B := (generic C₀).resultant (GenericProjectivePolarGcd.polar
    (ReceivedPolarContacts.dx (generic C₀)) (generic C₀).derivative (algebraMap k (RatFunc k) b)) 3 3
  change B ≠ 0 at hB
  have hBmap : (IntegralOrdinaryPolars.polarResultant C₀ (C b)).map m = B := resultant_eq C₀ b
  have hb : IntegralOrdinaryPolars.polarResultant C₀ (C b) ≠ 0 :=
    fun hz => hB (hBmap.symm.trans (by rw [hz, Polynomial.map_zero]))
  have hdg₀ := hpolar c b hcr hb
  have hgcd : OrdinaryPolarGcdBudget.genericDegree (IntegralOrdinaryPolars.polarResultant C₀ (C c))
      (IntegralOrdinaryPolars.polarResultant C₀ (C b)) = (GCDMonoid.gcd A B).natDegree := by
    exact (genericDegree_eq _ _).trans (congrArg
      (fun t : (RatFunc k)[X] => (GCDMonoid.gcd A t).natDegree) hBmap)
  have hdg := hdg₀.trans_eq (congrArg (fun q : ℕ => q+defect) hgcd)
  have hg : Bivariate.natWeightedDegree (generic C₀) 1 67108863 ≤ w := by
    apply Finset.sup_le
    intro j hj
    have hnj := mem_support_iff.mp hj
    change ((C₀.map (mapRingHom m)).coeff j) ≠ 0 at hnj
    rw [coeff_map] at hnj
    have hn : C₀.coeff j ≠ 0 := fun hz => hnj (by rw [hz, map_zero])
    change 1*((C₀.map (mapRingHom m)).coeff j).natDegree + 67108863*j ≤ w
    rw [one_mul, coeff_map, coe_mapRingHom]
    exact (Nat.add_le_add_right natDegree_map_le _).trans (hW j hn)
  have hweight := CubicPolarSiteBudget.weighted_degree_budget (generic C₀) hf 67108863 w
    (by omega) hg
  dsimp only [B] at hdg
  clear * - hbudget hweight hdg hw
  omega

/-- The rich terminal chart has defect 201. -/
theorem order_budget [Infinite k] [Differential (RatFunc k)]
    (C₀ : k[X][X][X]) (w p : ℕ) [CharP (RatFunc k) p]
    (hw : 201326589 ≤ w) (hp : 6*w-9*67108863-3 < p)
    (hW : ∀ j, C₀.coeff j ≠ 0 → (C₀.coeff j).natDegree + 67108863*j ≤ w)
    (hf : (generic C₀).natDegree = 3) (hprim : (generic C₀).IsPrimitive)
    (h₂ : (2 : RatFunc k) ≠ 0) (h₃ : (3 : RatFunc k) ≠ 0)
    (hV : (generic C₀).resultant (generic C₀).derivative 3 3 ≠ 0)
    (hH : (generic C₀).resultant (ScalarHessianLocalOrder.hessian (generic C₀)) 3 7 ≠ 0)
    (hpolar : ∀ c₁ c₂ : k, IntegralOrdinaryPolars.polarResultant C₀ (C c₁) ≠ 0 →
      IntegralOrdinaryPolars.polarResultant C₀ (C c₂) ≠ 0 →
      2*(w-67108863) ≤ OrdinaryPolarGcdBudget.genericDegree
        (IntegralOrdinaryPolars.polarResultant C₀ (C c₁))
        (IntegralOrdinaryPolars.polarResultant C₀ (C c₂)) + 201)
    (D : Finset (RatFunc k)) (l : RatFunc k → RatFunc k) (r : RatFunc k → ℕ)
    (hsite : ∀ α ∈ D, α′ = 0 ∧ (l α)′′ = 0 ∧ ∃ i, TruncatedJetMultipliers.Leader
      (ReceivedJetContact.shifted (generic C₀) α (l α)) (r α) i) :
    3*(∑ α ∈ D, r α) + 35*67108863 ≤ 2*D.card + 16*w + 402 := order_budget_of_defect C₀ w p 201 hw hp hW hf hprim h₂ h₃ hV hH hpolar D l r hsite

end ArkLib.ProximityGap.Frontier.IntegralPolarDescent

#print axioms ArkLib.ProximityGap.Frontier.IntegralPolarDescent.resultant_eq
#print axioms ArkLib.ProximityGap.Frontier.IntegralPolarDescent.genericDegree_eq
#print axioms ArkLib.ProximityGap.Frontier.IntegralPolarDescent.bounded_first

#print axioms ArkLib.ProximityGap.Frontier.IntegralPolarDescent.order_budget
