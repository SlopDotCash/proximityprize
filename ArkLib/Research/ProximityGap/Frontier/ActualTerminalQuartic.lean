/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalQuarticHessianTransport
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticWeightBound

/-! # Terminal quartic exclusion for the actual MCA witness family

A value-quartic irreducible divisor of the interpolation polynomial cannot
carry enough of the actual bad scalar labels at the production predecessor.
Both proper and flat Hessians are covered for the same raw polynomial.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.ActualTerminalQuartic

open TerminalQuarticLocalization TerminalQuarticHessianTransport JetMultiplierGraph
open IntrinsicReceivedSections IntrinsicQuarticSectionCap
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry

variable {K F ι : Type} [Field K] [Field F] [Fintype ι]

private theorem generic_flat_height (f : K[X][X][X]) (m : ℕ)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m) :
    Polynomial.Bivariate.degreeX (localPlane f) ≤ m := by
  apply Finset.sup_le
  intro j hj
  have hn : f.coeff j ≠ 0 := by
    intro hz
    apply (Polynomial.mem_support_iff.mp hj)
    simp only [localPlane,mapPlane,coeff_map,hz,map_zero]
  have he := hf j hn
  change ((localPlane f).coeff j).natDegree ≤ _
  simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom]
  exact natDegree_map_le.trans (by omega)

private theorem scalar_permute (f : K[X][X][X]) (m : ℕ)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m) : ScalarValueBound (permute f) m := by
  intro j a ha
  let q := ((permute f).coeff j).coeff a
  have hn : (f.coeff j) ≠ 0 := by
    intro hz
    apply ha
    simp [permute_coeff,hz]
  have he := hf j hn
  have hlead := leadingCoeff_ne_zero.mpr (show q ≠ 0 from ha)
  change q.coeff q.natDegree ≠ 0 at hlead
  have hs : ((f.coeff j).coeff q.natDegree).coeff a ≠ 0 := by
    rwa [← ApolarReciprocalCharts.swap_coeff,← permute_coeff]
  have hc : q.natDegree ≤ (f.coeff j).natDegree := le_natDegree_of_ne_zero (fun hz => hs (by simp [hz]))
  change q.natDegree+j ≤ m
  omega

private theorem coordinate_permute (f : K[X][X][X]) (d : ℕ) :
    Polynomial.Bivariate.natWeightedDegree (localPlane (permute f)) 1 d ≤
      SecondPrimeCoordinateWeight.weight d f := by
  apply Finset.sup_le
  intro j hj
  let q := (permute f).coeff j
  have hq : q ≠ 0 := by
    intro hz
    apply Polynomial.mem_support_iff.mp hj
    simp only [localPlane,mapPlane,coeff_map,show (permute f).coeff j=0 from hz,map_zero]
  have hh := leadingCoeff_ne_zero.mpr hq
  change q.coeff q.natDegree ≠ 0 at hh
  let A := q.coeff q.natDegree
  have hA := leadingCoeff_ne_zero.mpr (show A ≠ 0 from hh)
  change A.coeff A.natDegree ≠ 0 at hA
  have hc : ((f.coeff j).coeff A.natDegree).coeff q.natDegree ≠ 0 := by
    rwa [← ApolarReciprocalCharts.swap_coeff,← permute_coeff]
  have hd := SecondPrimeCoordinateWeight.coeff_weight_le d f hc
  change 1*((localPlane (permute f)).coeff j).natDegree+d*j ≤ _
  simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom,one_mul,
    natDegree_map_eq_of_injective (RatFunc.algebraMap_injective K)]
  simpa only [Nat.mul_comm j d] using hd

private theorem coeff_eval_permute (q : K[X][X]) (z : K) :
    (Bivariate.swap q).map (evalRingHom z) = q.eval (C z) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,Polynomial.map_add,hp,hq,eval_add]
  | monomial j A =>
    rw [Bivariate.swap_monomial,Polynomial.map_mul,Polynomial.map_map,eval_monomial,map_C]
    have hcomp : (evalRingHom z).comp (C : K →+* K[X]) = RingHom.id _ := by ext; simp
    rw [hcomp,Polynomial.map_id,coe_evalRingHom,eval_X_pow,C_pow]

private theorem proper_root (f : K[X][X][X]) (z : K) (q : K[X])
    (h : f.eval₂ (evalRingHom (C z)) q = 0) :
    (mapPlane (evalRingHom z) (permute f)).eval q = 0 := by
  have he : mapPlane (evalRingHom z) (permute f) = f.map (evalRingHom (C z)) := by
    apply Polynomial.ext
    intro j
    simp only [mapPlane,coeff_map,permute_coeff,coe_mapRingHom,coe_evalRingHom,coeff_eval_permute]
  rw [he,eval_map]
  exact h

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

/-- All scalar labels lying on the given original quartic factor of the
terminal interpolant, including the flat and proper alternatives. -/
theorem actual_quartic_label_cap [DecidableEq F] (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 276 < p) (dom : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (Q f : K[X][X][X]) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f)
    (hy : f.natDegree = 4)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34)
    (L : Finset F) (hL : L ⊆ fam.G)
    (hroot : ∀ z ∈ L, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    L.card ≤ 268435546 := by
  classical
  by_cases hlarge : 646 < L.card
  · have htotal := SecondPrimeSectionResultant.factor_triangle hQ hdiv htri
    have hw := SecondPrimeQuarticWeightBound.actual_quartic_weight φ dom δ u hn ht fam Q f
      hQ hdiv hi hy htri L hL hlarge hroot
    have hpos : 0 < f.natDegree := by omega
    have hj := local_generic f hi hpos
    have hin : Irreducible (permute f) := (MulEquiv.irreducible_iff permute).mpr hi
    have hf4 : (localPlane (permute f)).natDegree = 4 := by rw [local_degree,permute_degree,hy]
    by_cases hflat : MovingCubicVanishingBranch.genericEquation (localPlane (permute f)) ∣
        MovingCubicVanishingBranch.genericEquation (CanonicalQuarticSiteOrder.scalarFieldHessian
          (localPlane (permute f)))
    · have hc := ReverseHessianAffineSection.card_embedded_scalar_le_one ((RatFunc.C : K →+* RatFunc K).comp φ)
        (localPlane f) hj.2 hj.1 (by rw [local_degree,hy]; decide)
        (by rw [local_degree,hy]) (by rw [local_degree,hy]; omega)
        34 (generic_flat_height f 34 htotal) hp (flat_of_not_proper f hi hpos hflat) L (by
          intro z hz
          exact ⟨_,flat_root f (φ z) ((fam.q z).map φ) (hroot z hz)⟩)
      omega
    · let φe : F ↪ K := ⟨φ,φ.injective⟩
      let domK : ι ↪ K := dom.trans φe
      let D := (Finset.univ : Finset ι).map domK
      let uK (i : Fin 2) : K → K := Function.extend domK (fun x => φ (u i x)) (fun _ => 0)
      let qK : K → K[X] := Function.extend φ (fun z => (fam.q z).map φ) (fun _ => 0)
      have hr := local_generic (permute f) hin (by rwa [permute_degree])
      have hc := secondPrime_proper_quartic_label_cap (permute f) D (by simpa [D] using hn)
        (uK 0) (uK 1) (scalar_permute f 34 htotal) hr.1 hf4 hr.2 hflat
        ((coordinate_permute f 67108863).trans hw) (L.map φe) qK (by
          intro z hz
          obtain ⟨w,hw',rfl⟩ := Finset.mem_map.mp hz
          have hq : qK (φe w) = (fam.q w).map φ := φ.injective.extend_apply _ _ _
          rw [hq]
          let H := fullAgreement dom (u 0) (u 1) w (fam.q w)
          refine ⟨natDegree_map_le.trans (by have := fam.degree_lt w (hL hw'); omega),
            proper_root f (φ w) _ (hroot w hw'),H.map domK,?_,?_,?_⟩
          · exact Finset.map_subset_map.mpr (Finset.subset_univ _)
          · rw [Finset.card_map]
            exact ht.trans (fam.threshold_le w (hL hw'))
          · intro x hx
            obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
            have ha := congrArg φ (Finset.mem_filter.mp hi).2
            change ((fam.q w).map φ).eval (φ (dom i)) =
              uK 0 (domK i)+φ w*uK 1 (domK i)
            rw [eval_map_apply,show uK 0 (domK i)=φ (u 0 i) from domK.injective.extend_apply _ _ _,
              show uK 1 (domK i)=φ (u 1 i) from domK.injective.extend_apply _ _ _]
            simpa only [map_add,map_mul] using ha)
      simpa only [Finset.card_map] using hc
  · omega

end ArkLib.ProximityGap.Frontier.ActualTerminalQuartic

open ArkLib.ProximityGap.Frontier.ActualTerminalQuartic in
#print axioms actual_quartic_label_cap
