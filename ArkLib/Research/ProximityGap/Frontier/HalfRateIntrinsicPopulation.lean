/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReceivedHessianCharge
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReverseChart
import ArkLib.Research.ProximityGap.Frontier.HalfRateJetCapacity
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSelectedSectionChart

/-! # Unrestricted nonlinear section populations at the half-rate predecessor -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Module
namespace ArkLib.ProximityGap.Frontier.HalfRateIntrinsicPopulation
open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open TerminalQuarticHessianTransport TerminalQuarticLocalization IntrinsicReceivedSections
open JetMultiplierGraph QuarticIntrinsicAuxiliary IntrinsicCubicQuotientWindow
open IntrinsicCubicPopulation (originalOrder)
private abbrev s : ℕ := 536797744
private abbrev J : ℕ := 2523
private abbrev d : ℕ := 536870911
private abbrev T : ℕ := 1712*791228368
variable {K F I : Type} [Field K] [Field F] [Fintype I]

private theorem degree_floor (d : ℕ) (f : K[X][X][X]) (hf : f ≠ 0) :
    f.natDegree*d ≤ weight d f := by
  let a := f.coeff f.natDegree
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let b := a.coeff a.natDegree
  have hb : b ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h := coeff_weight_le d f (j := f.natDegree) (i := a.natDegree) (a := b.natDegree)
    (show b.coeff b.natDegree ≠ 0 from leadingCoeff_ne_zero.mpr hb)
  omega

set_option maxRecDepth 4096 in
/-- For every actual nonlinear component through degree four satisfying the reverse-Hessian
intersection inequality, the original selected labels use at most half the block length
per unit of value degree. The nonmultiple auxiliary and its section roots are constructed. -/
theorem population_of_charge (φ : F →+* K) (dom : I ↪ K) (u v : I → K)
    (hn : Fintype.card I = 1073741824) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (hR : (∑ i, let r := originalOrder f (dom i) (u i) (v i); r*(3*r-2)) +
      3*f.natDegree^2*d ≤ (6*f.natDegree-2)*weight d f)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, 791228368 ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) : G.card+5048 ≤ f.natDegree*536870912 := by
  classical
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
    (by rw [permute_degree]; omega)).1
  have hr (i : I) : r i ≤ f.natDegree := (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans hy.le
  have hU : finrank K U ≤ Fintype.card (Monomials (s-f.natDegree) J d (T-w)) :=
    finite_shifted_quotient_window f hi.ne_zero (by decide) f.natDegree
      (ArkLib.BivariateDegreeToolkit.natDegreeY_le_totalDegree f) (J+1)
      ((Nat.sub_le ..).trans (by decide : T ≤ (J+1)*d)) (by decide)
  have hcount := ProximityGap.HalfRateJetCapacity.strict_count r f.natDegree w hb₂ hb₄ hn hr
    (degree_floor d f hi.ne_zero) hw hR
  let cost (x : K) := let n := receivedOrder (permute f) x (uK x) (vK x)
    ((1712-n)*(1712-n+1)/2)*536797687
  have hsD : ∑ x ∈ D, cost x = ∑ i, ((1712-r i)*(1712-r i+1)/2)*536797687 := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    unfold cost
    rw [hu i,hv i]
    rfl
  have hdU := Nat.add_le_add_left hU (Fintype.card I*(1466328*536797745))
  rw [hn] at hdU
  have hbefore := hdU.trans_lt hcount
  have hV : finrank K V = Fintype.card (Monomials s J d T) := Module.finrank_pi K
  obtain ⟨c,hc,hs⟩ := exists_section_outside (μ := 1712) (s := s) D uK vK (permute f) hprim
    (SecondPrimeSelectedSectionChart.original_scalar_bound f htot) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
      rw [hu,hv]
      exact (hr i).trans (hb₄.trans (by decide))) (by decide) L (fun c => section_scalar_bound c (by decide)) U (by
        change D.card*(1466328*536797745)+finrank K U < finrank K V + ∑ x ∈ D, cost x
        rw [hsD,hV,Finset.card_map,Finset.card_univ,hn]
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
          exact (section_graph_degree c (φ z) (q z) hd (by decide)).trans_le (by
            change T ≤ H.card*1712
            unfold T
            omega))
    rw [← SecondPrimeSelectedSectionChart.section_identity]
    change (mapPlane (evalRingHom (φ z)) (permute (surface c))).eval (q z) = 0
    have hperm : permute (surface c) = sectionMap c := by
      rw [← permute_section]
      apply Polynomial.ext
      intro j
      rw [permute_coeff,permute_coeff,Bivariate.swap_swap_apply]
    rw [hperm]
    exact hzero
  · interval_cases hy : f.natDegree <;> dsimp [s,J] at hval ⊢ <;> omega

/-- Every nonlinear component of the actual half-rate interpolant saves at least 5,048
labels from its per-degree allocation. The proper reverse Hessian and geometric-line
branches are both included. -/
theorem population {p : ℕ} [CharP K p] (hp : 468 < p) (φ : F →+* K) (dom : I ↪ K)
    (u v : I → K) (hn : Fintype.card I = 1073741824) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, 791228368 ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) : G.card+5048 ≤ f.natDegree*536870912 := by
  classical
  by_cases hpH : IntrinsicCubicPopulation.Proper f
  · apply population_of_charge φ dom u v hn f hi hb₂ hb₄ htot hw _ G q hroot hfit
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
  · have hd : 0 < f.natDegree := by omega
    have he := local_generic f hi hd
    have hx : Bivariate.degreeX (localPlane f) ≤ 58 := by
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
      (by rw [local_degree]; omega) 58 hx hp (flat_of_not_proper f hi hd (Classical.not_not.mp hpH)) G
      (fun z hz => ⟨_,SecondPrimeReverseChart.root_in_reverse f (φ z) (q z) (hroot z hz)⟩)
    omega

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open scoped NNReal

/-- The cap on an original MCA family, after lifting its received pair and sections to
the extension field. All hypotheses on its agreement sets come from the family. -/
theorem actual_population [DecidableEq F] {p : ℕ} [CharP K p] (hp : 468 < p)
    (φ : F →+* K) (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824) (ht : 791228368 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 536870912 δ u) (f : K[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₄ : f.natDegree ≤ 4)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 58) (hw : weight d f ≤ 3*791228368-1)
    (G : Finset F) (hsub : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    G.card+5048 ≤ f.natDegree*536870912 := by
  let dk := dom.trans ⟨φ,φ.injective⟩
  apply population hp φ dk (fun i => φ (u 0 i)) (fun i => φ (u 1 i)) hn f hi hb₂ hb₄
    htot hw G (fun z => (fam.q z).map φ) hroot
  intro z hz
  refine ⟨natDegree_map_le.trans (by have := fam.degree_lt z (hsub hz); unfold d; omega),
    fullAgreement dom (u 0) (u 1) z (fam.q z), ht.trans (fam.threshold_le z (hsub hz)), ?_⟩
  intro i hi
  change ((fam.q z).map φ).eval (φ (dom i)) = _
  rw [eval_map_apply]
  exact (congrArg φ (Finset.mem_filter.mp hi).2).trans (by simp only [map_add,map_mul])

#print axioms population_of_charge
#print axioms population
#print axioms actual_population
end ArkLib.ProximityGap.Frontier.HalfRateIntrinsicPopulation
