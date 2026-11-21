/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfRateIntrinsicPopulation
import ArkLib.Research.ProximityGap.Frontier.HalfRateLinearPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface
import ArkLib.Research.ProximityGap.Frontier.ApolarHalfBreakpoint

/-! # The factor cover at the half-rate production predecessor -/

set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.HalfRatePopulationCover
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open SecondPrimeCoordinateWeight SecondPrimePrimitiveSurface

private theorem cover_bound {A B : Type} [DecidableEq A] [DecidableEq B]
    (U : Multiset A) (pop : A → Finset B) (deg : A → ℕ) (c : ℕ)
    (h : ∀ f ∈ U, (pop f).card ≤ deg f * c) :
    (U.toFinset.biUnion pop).card ≤ (U.map deg).sum * c := by
  induction U using Multiset.induction_on with
  | empty => simp
  | @cons f U ih =>
    rw [Multiset.toFinset_cons, insert_biUnion, Multiset.map_cons, Multiset.sum_cons, Nat.add_mul]
    exact (card_union_le ..).trans (Nat.add_le_add (h f (Multiset.mem_cons_self ..))
      (ih (fun g hg => h g (Multiset.mem_cons_of_mem hg))))

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [Nonempty I] [DecidableEq I]

/-- The original quartic covers the entire family,
including its vertical exceptions. The nonlinear components contribute at most 536869650
labels per unit of value degree. -/
theorem family_cap {p : ℕ} [CharP F p] (hp : 468 < p) (dom : I ↪ F) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) I) (hn : Fintype.card I = 1073741824)
    (ht : 791228368 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 536870912 δ u) :
    fam.G.card ≤ 2147478658 := by
  classical
  obtain ⟨Q, hQ, hshape, hroot⟩ := HalfRateUnrestrictedJetBudget.production_surface dom (u 0) (u 1) hn
  have hscalar (j : ℕ) : (Q.coeff j).natDegree ≤ 58 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext a
    simp only [coeff_zero]
    by_contra h
    have hbound := (hshape j i a h).2.1
    omega
  have hvalue : Q.natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (hshape j i a h).1
  have hweight : weight 536870911 Q ≤ 3*791228368-1 :=
    weight_le_of_coeff _ _ (fun j i a h => by have := (hshape j i a h).2.2; omega)
  have hsec (z : F) (hz : z ∈ fam.G) : Q.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    apply hroot z (fam.q z) (by have := fam.degree_lt z hz; omega)
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht.trans (fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  obtain ⟨P,E,hP,hprim,hPQ,hyP,_,hE,hret⟩ := primitive_surface (RingHom.id F) hQ fam.G fam.q 58
    hscalar hsec
  obtain ⟨U,hU,hsum,_,hcover⟩ := factor_cover P hP hprim
  have hd : (U.map natDegree).sum ≤ 4 := hsum.trans_le (hyP.trans_le hvalue)
  let pop (f : F[X][X][X]) := fam.G.filter fun z => f.eval₂ (evalRingHom (C z)) (fam.q z) = 0
  have covered : fam.G ⊆ E ∪ U.toFinset.biUnion pop := by
    intro z hz
    by_cases he : z ∈ E
    · exact mem_union_left _ he
    · obtain ⟨f,hf,hz'⟩ := hcover z (fam.q z) (hret z hz he)
      exact mem_union_right _ (mem_biUnion.mpr ⟨f,Multiset.mem_toFinset.mpr hf,mem_filter.mpr ⟨hz,hz'⟩⟩)
  have hpop (f : F[X][X][X]) (hf : f ∈ U) : (pop f).card ≤ f.natDegree*536869650 := by
    obtain ⟨hi,hpos,hfP⟩ := hU f hf
    have hfQ := hfP.trans hPQ
    have hle := (natDegree_le_of_dvd hfQ hQ).trans hvalue
    have hm := SecondPrimeSectionResultant.factor_triangle hQ hfQ (fun j i a h => (hshape j i a h).2.1)
    have hw : weight 536870911 f ≤ 3*791228368-1 := by
      obtain ⟨r,hr⟩ := hfQ
      have hr0 : r ≠ 0 := by intro h; rw [h,mul_zero] at hr; contradiction
      rw [hr,weight_mul _ _ _ hi.ne_zero hr0] at hweight
      omega
    have hsub : pop f ⊆ fam.G := filter_subset ..
    have hz (z : F) (hz : z ∈ pop f) := (mem_filter.mp hz).2
    by_cases hl : f.natDegree = 1
    · have hc := HalfRateLinearPopulation.actual_population (RingHom.id F) fam hn ht f hi hl hm
        (pop f) hsub (by simpa using hz)
      omega
    · have hc := HalfRateIntrinsicPopulation.actual_population (p := p) hp (RingHom.id F) dom δ u
        hn ht fam f hi (by omega) hle hm hw (pop f) hsub (by simpa using hz)
      omega
  have htotal := (card_le_card covered).trans (card_union_le ..)
  have hu := cover_bound U pop natDegree 536869650 hpop
  omega

open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open PrizeShapeRateHalfBracket
private abbrev n : ℕ := 1073741824

/-- Uniform line-MCA error probability at 282513456 errors on any injective
length-2³⁰ half-rate domain in characteristic greater than 468. -/
theorem eps_bound {p : ℕ} [CharP F p] (hp : 468 < p) (dom : I ↪ F) (hn : Fintype.card I = n) :
    epsMCA (F := F) (ReedSolomon.code dom 536870912 : Set (I → F)) ((282513456:ℝ≥0)/n) ≤
      (2147478658:ℝ≥0∞)/(Fintype.card F:ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le
  intro u
  let fam := canonicalBadScalarRichPointFamily dom (k := 536870912) ((282513456:ℝ≥0)/n) u (by decide)
  apply family_cap hp dom _ u hn _ fam
  rw [hn]
  have ht := TwoCorePackingThreshold.agreement_ceiling 282513456 (by decide)
  rw [Fintype.card_fin] at ht
  exact ht.ge

/-- The operational floor on the second production prime, including every positive
interleaving width. The scalar numerator is 4990 below the permitted count. -/
theorem second_prime_floor (width : ℕ) [NeZero width] :
    (282513457:ℝ≥0)/1073741824 ≤ mcaDeltaStar (F := ZMod PrizeShapePrimeP30Second.P)
      ((RateHalfApolarThreshold.code PrizeShapePrimeP30Second.g) ^⋈ (Fin width)) (epsStar:ℝ≥0∞) := by
  letI : Fact (Nat.Prime PrizeShapePrimeP30Second.P) := ⟨PrizeShapePrimeP30Second.prime_P⟩
  rw [mcaDeltaStar_interleaved_eq]
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a:=282513457) (by decide)
    (by decide : 282513457 ≤ n)
  let g := PrizeShapePrimeP30Second.g
  have hg := PrizeShapePrimeP30Second.orderOf_g
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom := KKH26RegimeSplit.powDomain g hg hg0
  have heq : RateHalfApolarThreshold.code g =
      (ReedSolomon.code dom 536870912 : Set (Fin n → ZMod PrizeShapePrimeP30Second.P)) :=
    KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 536870911
  rw [heq,epsStar_coe_eq_natCast_inv]
  apply (eps_bound (p:=PrizeShapePrimeP30Second.P) (by decide) dom (Fintype.card_fin _)).trans
  rw [ZMod.card]
  apply natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) PrizeShapePrimeP30Second.prime_P.pos
  exact (Nat.mul_le_mul_right _ (show 2147478658 ≤ PrizeShapePrimeP30Second.P/2^128 by
    rw [PrizeShapePrimeP30Second.P_div_two_pow_128]; decide)).trans (Nat.div_mul_le_self ..)

#print axioms family_cap
#print axioms eps_bound
#print axioms second_prime_floor
end ArkLib.ProximityGap.Frontier.HalfRatePopulationCover
