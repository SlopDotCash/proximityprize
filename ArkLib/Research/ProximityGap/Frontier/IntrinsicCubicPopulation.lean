/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicQuotientWindow
import ArkLib.Research.ProximityGap.Frontier.IntrinsicCubicWindowCount
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicOnly

/-! # Bounding actual cubic populations from their canonical joint multiplicity sum

The unrestricted auxiliary realizes every scalar/coordinate/value slot, removes
every multiple of the same raw cubic, and annihilates every selected section.
A proper scalar resultant then counts all distinct labels.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Module
open scoped NNReal BigOperators
namespace ArkLib.ProximityGap.Frontier.IntrinsicCubicPopulation

open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open TerminalQuarticHessianTransport TerminalQuarticLocalization IntrinsicReceivedSections
open JetMultiplierGraph QuarticIntrinsicAuxiliary IntrinsicCubicQuotientWindow
open IntrinsicCubicWindowCount (T d s quotientRows)

variable {K F I : Type} [Field K] [Field F] [Fintype I]

private theorem degree_floor (f : K[X][X][X]) (hf : f.natDegree = 3) :
    201326589 ≤ weight d f := by
  have hnF : f ≠ 0 := fun h => by simp [h] at hf
  let a := f.coeff 3
  have ha : a ≠ 0 := by
    change f.coeff 3 ≠ 0
    rw [← hf]
    exact leadingCoeff_ne_zero.mpr hnF
  let b := a.coeff a.natDegree
  have hb : b ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have h := coeff_weight_le d f (j := 3) (i := a.natDegree) (a := b.natDegree)
    (show b.coeff b.natDegree ≠ 0 from leadingCoeff_ne_zero.mpr hb)
  unfold d at h ⊢
  omega

private theorem scalar_bound_swap (f : K[X][X][X]) (m : ℕ)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m) : ScalarValueBound (permute f) m := by
  intro j a ha
  let q := ((permute f).coeff j).coeff a
  have hn : f.coeff j ≠ 0 := fun hz => ha (by simp [permute_coeff,hz])
  have hlead : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr ha
  have hs : ((f.coeff j).coeff q.natDegree).coeff a ≠ 0 := by
    rwa [← ApolarReciprocalCharts.swap_coeff,← permute_coeff]
  have hc : q.natDegree ≤ (f.coeff j).natDegree := le_natDegree_of_ne_zero (fun hz => hs (by simp [hz]))
  exact (Nat.add_le_add_right hc j).trans (hf j hn)

private theorem root_eq (P : K[X][X][X]) (z : K) (q : K[X]) :
    (mapPlane (evalRingHom z) (permute P)).eval q = P.eval₂ (evalRingHom (C z)) q := by
  have he : mapPlane (evalRingHom z) (permute P) = P.map (evalRingHom (C z)) := by
    apply Polynomial.ext
    intro j
    simp only [mapPlane,coeff_map,permute_coeff,coe_mapRingHom,coe_evalRingHom]
    simpa only [Polynomial.Bivariate.evalX_eq_map,Polynomial.Bivariate.evalY] using
      (Polynomial.Bivariate.evalY_eq_evalX_swap z (P.coeff j)).symm
  rw [he,eval_map]

/-- The actual multiplicity of the raw factor, in the scalar-first presentation
used by the polar and Hessian order estimates, on the original evaluation site. -/
def originalOrder (f : K[X][X][X]) (x u v : K) := receivedOrder (permute f) x u v

set_option maxRecDepth 4096 in
/-- The canonical ordinary-polar inequality suffices to bound every selected
section of an actual cubic on any production-sized received family. -/
theorem population_of_order (φ : F →+* K) (dom : I ↪ K) (u v : I → K)
    (hn : Fintype.card I = 1073741824) (f : K[X][X][X]) (hi : Irreducible f)
    (hf : f.natDegree = 3) (htot : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (hw : weight d f ≤ 290805098)
    (hR : 3*(∑ i, (originalOrder f (dom i) (u i) (v i) : ℤ)) ≤
      2*1073741824+16*(weight d f:ℤ)-35*67108863+532)
    (G : Finset F) (q : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (q z) = 0)
    (hfit : ∀ z ∈ G, (q z).natDegree ≤ d ∧ ∃ H : Finset I, 357913943 ≤ H.card ∧
      ∀ i ∈ H, (q z).eval (dom i) = u i+φ z*v i) : G.card ≤ 1200005270 := by
  classical
  let w := weight d f
  let k := quotientRows w
  let U := multiples (s := s) (b := 170) (d := d) (t := T) f
  let r (i : I) := originalOrder f (dom i) (u i) (v i)
  let V := IntrinsicCubicWindowCount.ProductionWindow → K
  let L : V →ₗ[K] K[X][X][X] := sectionMap
  let D := (Finset.univ : Finset I).map dom
  let uK := Function.extend dom u (fun _ => 0)
  let vK := Function.extend dom v (fun _ => 0)
  have hu (i : I) : uK (dom i) = u i := dom.injective.extend_apply _ _ _
  have hv (i : I) : vK (dom i) = v i := dom.injective.extend_apply _ _ _
  have hy : (localPlane (permute f)).natDegree = 3 := by rw [local_degree,permute_degree,hf]
  have hprim := (local_generic (permute f) ((MulEquiv.irreducible_iff permute).mpr hi)
    (by rw [permute_degree,hf]; decide)).1
  have hr (i : I) : r i ≤ 3 := (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans hy.le
  have hjk := IntrinsicCubicWindowCount.quotient_rows w hw
  have hU : finrank K U ≤ Fintype.card (Monomials s (k-1) d (T-w)) :=
    finite_quotient_window f hi.ne_zero (by decide) k hjk.2.2 hjk.1
  have hcount := IntrinsicCubicWindowCount.strict_count r w hn hr (degree_floor f hf) hw hR
  let cost (x : K) := let n := receivedOrder (permute f) x (uK x) (vK x)
    ((32-n)*(32-n+1)/2)*399999967
  have hsD : ∑ x ∈ D, cost x = ∑ i, ((32-r i)*(32-r i+1)/2)*399999967 := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    unfold cost
    rw [hu i,hv i]
    rfl
  have hdU := Nat.add_le_add_left hU (Fintype.card I*(528*400000001))
  have hbefore := hdU.trans_lt hcount
  have hV : finrank K V = Fintype.card IntrinsicCubicWindowCount.ProductionWindow := Module.finrank_pi K
  obtain ⟨c,hc,hs⟩ := exists_section_outside (μ := 32) (s := s) D uK vK (permute f) hprim
    (scalar_bound_swap f 34 htot) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
      rw [hu,hv]
      exact (hr i).trans (by decide)) (by decide) L (fun c => section_scalar_bound c (by decide)) U (by
        change D.card*(528*400000001)+finrank K U < finrank K V + ∑ x ∈ D, cost x
        rw [hsD,hV,Finset.card_map,Finset.card_univ]
        exact hbefore)
  have hnd : ¬ f ∣ surface c := fun hd => hc ((mem_multiples f c).mpr hd)
  have hnC : c ≠ 0 := by intro h; apply hc; rw [h]; exact U.zero_mem
  have hC := surface_ne_zero hnC
  have hsh := SecondPrimeSectionResultant.factor_triangle hC (dvd_refl (surface c))
    (fun j i a hn => (surface_support c hn).2.1)
  have hval : (surface c).natDegree ≤ 170 := by
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
      ((root_eq f (φ z) (q z)).trans (hroot z hz)) (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
        simpa only [hu,hv] using ha i hi) (by
          rw [Finset.card_map]
          exact (section_graph_degree c (φ z) (q z) hd (by decide)).trans_le (by
            change T ≤ H.card*32
            unfold T
            omega))
    rw [← root_eq]
    have hperm : permute (surface c) = sectionMap c := by
      rw [← permute_section]
      apply Polynomial.ext
      intro j
      rw [permute_coeff,permute_coeff,Bivariate.swap_swap_apply]
    rw [hperm]
    exact hzero
  · rw [hf]
    unfold s
    omega

/-- Total joint multiplicity on the original finite domain and received stack. -/
def totalOrder (φ : F →+* K) (dom : I ↪ F) (u : Code.WordStack F (Fin 2) I)
    (f : K[X][X][X]) : ℕ :=
  ∑ i, originalOrder f (φ (dom i)) (φ (u 0 i)) (φ (u 1 i))

/-- Proper-intersection branch for the very same raw cubic. -/
def Proper (f : K[X][X][X]) : Prop :=
  ¬MovingCubicVanishingBranch.genericEquation (localPlane (permute f)) ∣
    MovingCubicVanishingBranch.genericEquation (CanonicalQuarticSiteOrder.scalarFieldHessian
      (localPlane (permute f)))

private theorem flat_height (f : K[X][X][X]) (hf : WeightedSylvesterDegree.TotalDegreeLe f 34) :
    Polynomial.Bivariate.degreeX (localPlane f) ≤ 34 := by
  apply Finset.sup_le
  intro j hj
  have hn : f.coeff j ≠ 0 := by
    intro hz
    apply Polynomial.mem_support_iff.mp hj
    simp only [localPlane,mapPlane,coeff_map,hz,map_zero]
  have he := hf j hn
  change ((localPlane f).coeff j).natDegree ≤ _
  simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom]
  exact natDegree_map_le.trans (by omega)

private theorem flat_root (f : K[X][X][X]) (z : K) (q : K[X])
    (h : f.eval₂ (evalRingHom (C z)) q = 0) :
    ((localPlane f).map (evalRingHom (RatFunc.C z))).eval (algebraMap K[X] (RatFunc K) q) = 0 := by
  let θ := algebraMap K[X] (RatFunc K)
  have he : (localPlane f).map (evalRingHom (RatFunc.C z)) =
      (f.map (evalRingHom (C z))).map θ := by
    apply Polynomial.ext
    intro j
    simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom,coe_evalRingHom]
    change ((f.coeff j).map θ).eval (θ (C z)) = θ ((f.coeff j).eval (C z))
    rw [eval_map_apply]
  rw [he,eval_map_apply,eval_map,h,map_zero]

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry SecondPrimeActualPopulations

/-- The order estimate is needed only on a proper, populated original cubic.
Every other geometric and dimension condition here is derived from Q. -/
theorem actual_cubic_population_at [DecidableEq F] (φ : F →+* K) {p : ℕ} [CharP K p] (hp : 276 < p)
    (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824) (ht : 357913943 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u) (Q f : K[X][X][X]) (hQ : Q ≠ 0)
    (hi : Irreducible f) (hd : f ∣ Q) (hf : f.natDegree = 3)
    (hs : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34)
    (hw : weight d f ≤ 290805098)
    (cutoff : ℕ) (hc : 1200005270 < cutoff)
    (hR : Proper f → cutoff ≤ (population fam φ f).card →
      3*(totalOrder φ dom u f:ℤ) ≤ 2*1073741824+16*(weight d f:ℤ)-35*67108863+532) :
    (population fam φ f).card < cutoff := by
  classical
  by_contra! hlarge
  have htotal := SecondPrimeSectionResultant.factor_triangle hQ hd hs
  let G := population fam φ f
  have hG : G ⊆ fam.G := Finset.filter_subset _ _
  have hroot (z : F) (hz : z ∈ G) :
      f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := (Finset.mem_filter.mp hz).2
  by_cases hproper : Proper f
  · have hR' := hR hproper hlarge
    let dk : I ↪ K := dom.trans ⟨φ,φ.injective⟩
    have hsum (v : I → ℕ) : (∑ i, (v i : ℤ)) = ((∑ i, v i : ℕ):ℤ) := (Nat.cast_sum ..).symm
    have hc := population_of_order φ dk (fun i => φ (u 0 i)) (fun i => φ (u 1 i)) hn f hi hf htotal hw
      (by rw [hsum]; exact hR') G (fun z => (fam.q z).map φ) hroot (by
        intro z hz
        refine ⟨natDegree_map_le.trans (by have := fam.degree_lt z (hG hz); unfold d; omega),
          fullAgreement dom (u 0) (u 1) z (fam.q z),ht.trans (fam.threshold_le z (hG hz)),?_⟩
        intro i hi
        change ((fam.q z).map φ).eval (φ (dom i)) = _
        rw [eval_map_apply]
        exact (congrArg φ (Finset.mem_filter.mp hi).2).trans (by simp only [map_add,map_mul]))
    exact (show ¬ cutoff ≤ 1200005270 by omega) (hlarge.trans hc)
  · have hflat := Classical.not_not.mp (show ¬¬_ from hproper)
    have he := local_generic f hi (by omega)
    have hh := ReverseHessianAffineSection.card_embedded_scalar_le_one ((RatFunc.C : K →+* RatFunc K).comp φ)
      (localPlane f) he.2 he.1 (by rw [local_degree,hf]; decide) (by rw [local_degree,hf]; decide)
      (by rw [local_degree,hf]; omega) 34 (flat_height f htotal) hp (flat_of_not_proper f hi (by omega) hflat) G
      (fun z hz => ⟨_,flat_root f (φ z) ((fam.q z).map φ) (hroot z hz)⟩)
    exact (show ¬ cutoff ≤ 1 by omega) (hlarge.trans hh)

/-- A uniform received-order estimate excludes the named terminal population. -/
theorem actual_cubic_population [DecidableEq F] (φ : F →+* K) {p : ℕ} [CharP K p] (hp : 276 < p)
    (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824) (ht : 357913943 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u) (Q f : K[X][X][X]) (hQ : Q ≠ 0)
    (hi : Irreducible f) (hd : f ∣ Q) (hf : f.natDegree = 3)
    (hs : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34)
    (hw : weight d f ≤ 290805098)
    (hR : Proper f → 1431655733 ≤ (population fam φ f).card →
      3*(totalOrder φ dom u f:ℤ) ≤ 2*1073741824+16*(weight d f:ℤ)-35*67108863+532) :
    (population fam φ f).card < 1431655733 :=
  actual_cubic_population_at φ hp dom δ u hn ht fam Q f hQ hi hd hf hs hw 1431655733 (by decide) hR

end ArkLib.ProximityGap.Frontier.IntrinsicCubicPopulation

open ArkLib.ProximityGap.Frontier.IntrinsicCubicPopulation in
#print axioms population_of_order
open ArkLib.ProximityGap.Frontier.IntrinsicCubicPopulation in
#print axioms actual_cubic_population

namespace ProximityGap.SecondPrimeCubicOnly

open ArkLib.ProximityGap.Frontier
open IntrinsicCubicPopulation SecondPrimeCoordinateWeight SecondPrimeActualPopulations
open HalfPredecessorBadEventRichPointBridge TerminalCollinearHeadCount
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped ENNReal

private abbrev pOrder := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev gOrder := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact pOrder.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The ordinary-polar inequality for the canonical sum on a single populous
proper cubic is sufficient for the exact named second-prime threshold. -/
theorem secondPrime_threshold_of_received_order
    (h : ∀ u : Code.WordStack (ZMod pOrder) (Fin 2) (Fin (2^30)),
      let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
        ((715827881 : ℝ≥0)/1073741824) u (by decide)
      let φ := algebraMap (ZMod pOrder) (AlgebraicClosure (ZMod pOrder))
      ∀ Q f : Factor (AlgebraicClosure (ZMod pOrder)), Q ≠ 0 → TerminalFactorCoverage.Supported Q →
        Irreducible f → f ∣ Q → f.natDegree = 3 → weight 67108863 f ≤ 290805098 →
        Proper f → 1431655733 ≤ (population fam φ f).card →
        3*totalOrder φ secondDomain u f+35*67108863 ≤ 2*1073741824+16*weight 67108863 f+532) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod pOrder) (evalCode gOrder (2^30) (2^26-1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0)/1073741824 := by
  apply secondPrime_threshold_of_cubic_exclusion
  intro u fam φ Q f hQ hs hi hd hy hw
  apply actual_cubic_population φ (p := pOrder) (by decide) secondDomain _ u (Fintype.card_fin _)
    ((TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)).ge) fam Q f hQ hi hd hy
    (fun j i a he => (hs j i a he).2.1) hw
  intro hp hM
  have he := h u Q f hQ hs hi hd hy hw hp hM
  have he' : (3:ℤ)*totalOrder φ secondDomain u f+35*67108863 ≤
      2*1073741824+16*(weight 67108863 f:ℤ)+532 := by exact_mod_cast he
  change (3:ℤ)*totalOrder φ secondDomain u f ≤ 2*1073741824+16*(weight 67108863 f:ℤ)-35*67108863+532
  omega

end ProximityGap.SecondPrimeCubicOnly

open ProximityGap.SecondPrimeCubicOnly in
#print axioms secondPrime_threshold_of_received_order
