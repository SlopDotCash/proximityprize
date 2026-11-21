/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReceivedHessianCharge
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReverseChart
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicQuotientWindow
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSelectedSectionChart

/-! # A general unrestricted-jet bound for nonlinear section populations -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Module
namespace ArkLib.ProximityGap.Frontier.UnrestrictedSectionPopulation
open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open TerminalQuarticHessianTransport TerminalQuarticLocalization IntrinsicReceivedSections
open JetMultiplierGraph QuarticIntrinsicAuxiliary IntrinsicCubicQuotientWindow
open IntrinsicCubicPopulation (originalOrder)
variable {K F I : Type} [Field K] [Field F] [Fintype I]

theorem degree_floor (d : ℕ) (f : K[X][X][X]) (hf : f ≠ 0) :
    f.natDegree*d ≤ weight d f := by
  let a := f.coeff f.natDegree
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let b := a.coeff a.natDegree
  have hb : b ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h := coeff_weight_le d f (j := f.natDegree) (i := a.natDegree) (a := b.natDegree)
    (show b.coeff b.natDegree ≠ 0 from leadingCoeff_ne_zero.mpr hb)
  omega

/-- A strict dimension surplus produces an auxiliary outside the multiples of the component.
The scalar resultant bounds the number of rich polynomial sections on that component. -/
theorem population_of_capacity {s J d t μ m : ℕ} (hT : 0 < μ*t) (hJ : μ*t ≤ (J+1)*d)
    (hJs : J ≤ s) (hm : m ≤ s+1) (φ : F →+* K) (dom : I ↪ K) (u v : I → K)
    (f : K[X][X][X]) (hi : Irreducible f) (hb : 0 < f.natDegree) (hbμ : f.natDegree ≤ μ)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f m)
    (hcount : Fintype.card I * ((μ*(μ+1)/2)*(s+1)) +
        Fintype.card (Monomials (s-f.natDegree) J d (μ*t-weight d f)) <
      Fintype.card (Monomials s J d (μ*t)) +
        ∑ i, let r := originalOrder f (dom i) (u i) (v i); ((μ-r)*(μ-r+1)/2)*(s+1-m))
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, t ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) :
    G.card ≤ f.natDegree*s + J*(m-f.natDegree) := by
  classical
  let T := μ*t
  let w := weight d f
  let U := multiples (s := s) (b := J) (d := d) (t := T) f
  let r (i : I) := originalOrder f (dom i) (u i) (v i)
  let V := (Monomials s J d T) → K
  let L : V →ₗ[K] K[X][X][X] := sectionMap
  let D := (Finset.univ : Finset I).map dom
  let uK := Function.extend dom u (fun _ => 0)
  let vK := Function.extend dom v (fun _ => 0)
  have hu (i : I) : uK (dom i) = u i := dom.injective.extend_apply _ _ _
  have hv (i : I) : vK (dom i) = v i := dom.injective.extend_apply _ _ _
  have hy : (localPlane (permute f)).natDegree = f.natDegree := by rw [local_degree,permute_degree]
  have hprim := (local_generic (permute f) ((MulEquiv.irreducible_iff permute).mpr hi)
    (by rwa [permute_degree])).1
  have hr (i : I) : r i ≤ f.natDegree := (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans hy.le
  have hU : finrank K U ≤ Fintype.card (Monomials (s-f.natDegree) J d (T-w)) :=
    finite_shifted_quotient_window f hi.ne_zero hT f.natDegree
      (ArkLib.BivariateDegreeToolkit.natDegreeY_le_totalDegree f) (J+1)
      ((Nat.sub_le ..).trans hJ) (by omega)
  let cost (x : K) := let n := receivedOrder (permute f) x (uK x) (vK x)
    ((μ-n)*(μ-n+1)/2)*(s+1-m)
  have hsD : ∑ x ∈ D, cost x = ∑ i, ((μ-r i)*(μ-r i+1)/2)*(s+1-m) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    unfold cost
    rw [hu i,hv i]
    rfl
  have hdU := Nat.add_le_add_left hU (Fintype.card I*((μ*(μ+1)/2)*(s+1)))
  have hbefore := hdU.trans_lt hcount
  have hV : finrank K V = Fintype.card (Monomials s J d T) := Module.finrank_pi K
  obtain ⟨c,hc,hs⟩ := exists_section_outside (μ := μ) (s := s) D uK vK (permute f) hprim
    (SecondPrimeSelectedSectionChart.original_scalar_bound f htot) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
      rw [hu,hv]
      exact (hr i).trans hbμ) hm L (fun c => section_scalar_bound c hJs) U (by
        change D.card*((μ*(μ+1)/2)*(s+1))+finrank K U < finrank K V + ∑ x ∈ D, cost x
        rw [hsD,hV,Finset.card_map,Finset.card_univ]
        exact hbefore)
  have hnd : ¬ f ∣ surface c := fun hd => hc ((mem_multiples f c).mpr hd)
  have hnC : c ≠ 0 := by intro h; apply hc; rw [h]; exact U.zero_mem
  have hC := surface_ne_zero hnC
  have hsh := SecondPrimeSectionResultant.factor_triangle hC (dvd_refl (surface c))
    (fun j i a hn => (surface_support c hn).2.1)
  have hval : (surface c).natDegree ≤ J := by
    rw [← permute_section c,permute_degree]
    exact section_value_degree c
  by_contra! hbig
  apply hnd
  apply SecondPrimeSectionResultant.divides_of_many_sections φ f (surface c) hi (by omega)
    htot hsh G q
  · intro z hz
    refine ⟨hroot z hz,?_⟩
    obtain ⟨hd,H,hH,ha⟩ := hfit z hz
    have hzero := hs (φ z) (q z) (H.map dom) (Finset.map_subset_map.mpr (Finset.subset_univ _))
      ((SecondPrimeSelectedSectionChart.section_identity f (φ z) (q z)).trans (hroot z hz)) (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
        simpa only [hu,hv] using ha i hi) (by
          rw [Finset.card_map]
          exact (section_graph_degree c (φ z) (q z) hd hT).trans_le (by
            change T ≤ H.card*μ
            exact (Nat.mul_comm ..).le.trans (Nat.mul_le_mul_right μ hH)))
    rw [← SecondPrimeSelectedSectionChart.section_identity]
    change (mapPlane (evalRingHom (φ z)) (permute (surface c))).eval (q z) = 0
    have hperm : permute (surface c) = sectionMap c := by
      rw [← permute_section]
      apply Polynomial.ext
      intro j
      rw [permute_coeff,permute_coeff,Bivariate.swap_swap_apply]
    rw [hperm]
    exact hzero
  · have hm' : f.natDegree ≤ m := by
      have h := htot f.natDegree (show f.coeff f.natDegree ≠ 0 from leadingCoeff_ne_zero.mpr hi.ne_zero)
      omega
    have hle := Nat.mul_le_mul_right (m-f.natDegree) hval
    rw [Nat.mul_sub, Nat.mul_comm (surface c).natDegree f.natDegree] at hle
    have hmul := Nat.mul_le_mul_left (surface c).natDegree hm'
    rw [Nat.mul_comm (surface c).natDegree f.natDegree] at hmul
    omega

/-- The component either satisfies the intrinsic order charge or has at most one scalar section. -/
theorem charge_or_singleton {m d p : ℕ} [CharP K p] (hp : 8*m+4 < p) (φ : F →+* K)
    (dom : I ↪ K) (u v : I → K) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f m)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0) :
    (∑ i, let r := originalOrder f (dom i) (u i) (v i); r*(3*r-2)) +
      3*f.natDegree^2*d ≤ (6*f.natDegree-2)*weight d f ∨ G.card ≤ 1 := by
  classical
  by_cases hpH : IntrinsicCubicPopulation.Proper f
  · left
    let V := (univ : Finset I).map dom
    let uK := Function.extend dom u (fun _ => 0)
    let vK := Function.extend dom v (fun _ => 0)
    have hu (i : I) : uK (dom i) = u i := dom.injective.extend_apply _ _ i
    have hv (i : I) : vK (dom i) = v i := dom.injective.extend_apply _ _ i
    have hb := ReceivedHessianCharge.received_charge (SecondPrimeScalarChart.scalarChart f)
      f.natDegree d (weight d f) hb₂ (SecondPrimeScalarChart.value_degree f)
      (SecondPrimeScalarChart.generic_irreducible f hi (by omega)) hpH
      (degree_floor d f hi.ne_zero) (SecondPrimeScalarChart.chart_weight f d) V uK vK
    have heq : SecondPrimeScalarChart.scalarChart f = localPlane (permute f) := rfl
    rw [Finset.sum_map,heq] at hb
    simpa only [originalOrder,receivedOrder,localPlane,received,map_add,map_mul,RatFunc.algebraMap_C,
      RatFunc.algebraMap_X,hu,hv] using hb
  · right
    have hd : 0 < f.natDegree := by omega
    have he := local_generic f hi hd
    have hx : Bivariate.degreeX (localPlane f) ≤ m := by
      apply Finset.sup_le
      intro j hj
      have hne : f.coeff j ≠ 0 := by
        intro hz
        exact Polynomial.mem_support_iff.mp hj (by simp [localPlane,mapPlane,hz])
      have h := htot j hne
      change ((localPlane f).coeff j).natDegree ≤ _
      simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom]
      exact natDegree_map_le.trans (by omega)
    have hh := ReverseHessianAffineSection.card_embedded_scalar_le_one ((RatFunc.C : K →+* RatFunc K).comp φ)
      (localPlane f) he.2 he.1 (by rwa [local_degree]) (by rwa [local_degree])
      (by rw [local_degree]; omega) m hx hp (flat_of_not_proper f hi hd (Classical.not_not.mp hpH)) G
      (fun z hz => ⟨_,SecondPrimeReverseChart.root_in_reverse f (φ z) (q z) (hroot z hz)⟩)
    exact hh

#print axioms population_of_capacity
#print axioms charge_or_singleton
end ArkLib.ProximityGap.Frontier.UnrestrictedSectionPopulation
