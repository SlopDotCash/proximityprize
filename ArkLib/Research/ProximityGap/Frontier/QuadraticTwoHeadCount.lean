/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # Two-head upper bounds from value-quadratic interpolation at variable lengths

A triangular interpolant of scalar-value degree 34 and ordinate degree two
has a strict coefficient surplus precisely above its stated linear threshold.
At rates up to one third every sufficiently populated factor is a head.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.QuadraticTwoHeadCount

open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private theorem capacity {n d t : ℕ} (surplus : 35*n+100*d < 102*t) :
    n*(34+1) < Fintype.card (Monomials 34 2 d t) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

set_option maxRecDepth 8192 in
/-- At any rate through one third, the triangular surplus and a positive
error budget force all bad labels into at most two secants. -/
theorem family_cap_weighted {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) {n e t t₀ : ℕ}
    (hn : Fintype.card I=n) (hsum : e+t=n) (hk : 1≤k) (rate : 3*k≤n)
    (he : 2080 < e) (htmin : t₀≤t) (surplus : 35*n+100*(k-1)<102*t₀)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hchar : ∀ i : ℕ, 0 < i → i≤2*(t₀-1-(k-1)) → (i:F)≠0) :
    fam.G.card ≤ 2*e+2 := by
  classical
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m := 478) (t := t₀) fam hk (by decide)
      _ M hM hm U hn (htmin.trans ht.ge)
    intro c a b l v hc hinc hcover ha hb hl
    omega
  obtain ⟨c, hc, _, witness⟩ := exists_curve (s := 34) (v := 2) (d := (k-1)) dom (u 0) (u 1) (by omega : 0 < t₀)
    (by rw [hn]; exact capacity surplus)
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have shape {j i a : ℕ} (h : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 2 ∧ i+j ≤ 34 ∧ a+j*(k-1) < t₀ := surface_support c h
  have scalar (j : ℕ) : (Q.coeff j).natDegree ≤ 34 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext a
    simp only [coeff_zero]
    by_contra h
    have := (shape h).2.1
    omega
  have val : Q.natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (shape h).1
  let φ := RingHom.id F
  let pop (f : F[X][X][X]) := fam.G.filter fun z =>
    f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  have population_eq (f : F[X][X][X])
      (d : DecidablePred fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
      @Finset.filter F _ d fam.G = pop f := by
    ext z
    simp only [pop, mem_filter]
  have roots (z : F) (hz : z ∈ fam.G) :
      Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    simp only [Q, φ, Polynomial.map_id, RingHom.id_apply, surface_eval]
    apply witness _ _ (by have := fam.degree_lt z hz; omega) (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (htmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  obtain ⟨P,E,hP,prim,hPQ,hval,_,hE,after⟩ := SecondPrimePrimitiveSurface.primitive_surface
    φ hQ fam.G (fun z => (fam.q z).map φ) 34 scalar roots
  obtain ⟨U, factors, _, hnum, hits⟩ := SecondPrimePrimitiveSurface.factor_cover P hP prim
  let V := U.toFinset
  have hV : V.card ≤ 2 := U.toFinset_card_le.trans (hnum.trans (hval.le.trans val))
  have cover (z : F) (hz : z ∈ fam.G) (he : z ∉ E) : ∃ f ∈ V, z ∈ pop f := by
    obtain ⟨f, hf, hroot⟩ := hits _ _ (after z hz he)
    exact ⟨f, Multiset.mem_toFinset.mpr hf, mem_filter.mpr ⟨hz,hroot⟩⟩
  let zmin := t - n/1024
  apply TwoLargeCoreCount.card_le_two_mul_add_two fam (zmin := zmin) hk (by omega)
    (hn.trans hsum.symm) ht (by rw [hn]; dsimp [zmin]; omega)
  intro H hH hsize
  have some_large : ∃ f ∈ V, 1024 < (H ∩ pop f).card := by
    by_contra! hall
    have hsub : H ⊆ E ∪ V.biUnion (fun f => H ∩ pop f) := by
      intro z hz
      by_cases ze : z ∈ E
      · exact mem_union_left _ ze
      · obtain ⟨f,hf,hzpop⟩ := cover z (hH hz) ze
        exact mem_union_right _ (mem_biUnion.mpr ⟨f,hf,mem_inter.mpr ⟨hz,hzpop⟩⟩)
    have htotal := (card_le_card hsub).trans ((card_union_le ..).trans
      (Nat.add_le_add_left card_biUnion_le E.card))
    have hc := sum_le_sum hall
    simp only [sum_const,smul_eq_mul] at hc
    omega
  obtain ⟨f,hf,hbig⟩ := some_large
  obtain ⟨hirr,hpos,hdiv⟩ := factors f (Multiset.mem_toFinset.mp hf)
  have hdivQ := hdiv.trans hPQ
  have hd := (natDegree_le_of_dvd hdivQ hQ).trans val
  have hpop : 1024 < (pop f).card := hbig.trans_le (card_le_card inter_subset_right)
  have htot := factor_totalDegree_le hQ hdivQ (fun _ _ _ h => (shape h).2.1)
  have hlin : f.natDegree = 1 := by
    by_contra hnon
    have hquad : f.natDegree = 2 := by omega
    have hbound := SecondPrimeQuadraticFactor.quadratic_population_weighted
      (d := k-1) (w := t₀-1) (m := 511) fam φ Q f hQ hdivQ hirr hquad
      (fun _ _ _ h => ⟨(shape h).2.1, by have := (shape h).2.2; omega⟩)
      (by omega) (by omega) hchar extract
    rw [population_eq f] at hbound
    omega
  obtain ⟨p,hp,hcarry⟩ := linear_factor_is_head_of_extraction (m := 511) fam φ f hirr hlin
    htot extract (by rw [population_eq f]; omega)
  rw [population_eq f] at hcarry
  have hcar : H ∩ pop f ⊆ pointsOn fam p := inter_subset_right.trans hcarry
  have hL : 1024 ≤ (pointsOn fam p).card := hbig.le.trans (card_le_card hcar)
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < (H ∩ pop f).card by omega)
  refine ⟨a,(mem_inter.mp ha).1,b,(mem_inter.mp hb).1,hab,?_⟩
  rw [secantParameter_eq_of_mem_pointsOn fam p (hcar ha) (hcar hb) hab]
  have pack := pointsOn_card_mul_max_add_core_le fam hp
  rw [ht,hn] at pack
  let core := (jointCore dom (u 0) (u 1) p.1 p.2).card
  have packed : 1024 * (t-core) ≤ n :=
    (Nat.mul_le_mul hL (le_max_right 1 (t-core))).trans (by exact (Nat.le_add_right _ _).trans pack)
  change t - n/1024 ≤ core
  omega

/-- Unweighted characteristic bound for existing callers. -/
theorem family_cap {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) {n e t t₀ : ℕ}
    (hn : Fintype.card I=n) (hsum : e+t=n) (hk : 1≤k) (rate : 3*k≤n)
    (he : 2080 < e) (htmin : t₀≤t) (surplus : 35*n+100*(k-1)<102*t₀)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hchar : ∀ i : ℕ, 0 < i → i≤2*(t₀-1) → (i:F)≠0) :
    fam.G.card ≤ 2*e+2 :=
  family_cap_weighted fam hn hsum hk rate he htmin surplus ht
    (fun i hi bound => hchar i hi (by omega))

end ArkLib.ProximityGap.Frontier.QuadraticTwoHeadCount
#print axioms ArkLib.ProximityGap.Frontier.QuadraticTwoHeadCount.family_cap
