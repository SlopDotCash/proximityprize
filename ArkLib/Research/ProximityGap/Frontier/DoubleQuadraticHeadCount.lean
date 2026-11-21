/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuadraticFactor
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # A variable-degree quadratic interpolant with a double auxiliary
The primary surface has degree two in the folded value. A factor supporting
more than the resultant degree divides a second surface of scalar/value
degree sixteen. Thus the discriminant and affine extraction estimates apply
even when the primary scalar degree is large.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount

open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
  {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}


private theorem simple_capacity {s n d t : ℕ} (hs : 2 ≤ s) (hd : 2*d ≤ t)
    (surplus : (s+1)*n+(3*s-2)*d < 3*s*t) :
    n*(s+1) < Fintype.card (Monomials s 2 d t) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  have a : s+1-1=s := by omega
  have b : s+1-2=s-1 := by omega
  have c : t-d+d=t := by omega
  have e : t-2*d+2*d=t := by omega
  have h : 3*s-2+2=3*s := by omega
  have f : s-1+1=s := by omega
  nlinarith only [surplus, congrArg (·*d) h,congrArg (·*(t-d)) a,congrArg (·*(t-2*d)) b,
    congrArg (s*·) c, congrArg ((s-1)*·) e,congrArg (·*t) f,congrArg (·*d) f]

private theorem double_capacity {n d t : ℕ} (surplus : 50*n+140*d<150*t) :
    n*(2*(16+1)+16)<Fintype.card (Monomials 16 4 d (2*t)) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  omega

set_option maxRecDepth 8192 in
/-- Variable-degree primary interpolation gives the full two-head bound
when both interpolation surpluses and the scalar and core tests hold. -/
theorem family_cap {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) {n e t t₀ s L : ℕ}
    (hn : Fintype.card I=n) (hsum : e+t=n) (hk : 1 ≤ k) (hmin : t₀ ≤ t)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hs : 2 ≤ s) (hd : 2*(k-1) ≤ t₀) (hsur : (s+1)*n+(3*s-2)*(k-1)<3*s*t₀)
    (hdouble : 50*n+140*(k-1)<150*t₀) (hbase : n+3*(k-1) ≤ 3*t₀)
    (hL : 512 ≤ L) (hresult : 4*s+32 ≤ L) (enough : s+2*L<e+2)
    (geom : n+3*(k-1)<t+2*(t-n/L))
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 2*(t₀-1) → (i:F) ≠ 0) :
    fam.G.card ≤ 2*e+2 := by
  classical
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m:=478) (t:=t₀) fam hk (by decide) _ M hM hm U hn (hmin.trans ht.ge)
    intro c a b l v hc hinc hcover ha hb hl
    omega
  obtain ⟨c,hc,_,witness⟩ := exists_curve (s:=s) (v:=2) (d:=k-1) dom (u 0) (u 1)
    (by omega : 0<t₀) (by rw [hn];exact simple_capacity hs hd hsur)
  obtain ⟨c₂,hc₂,witness₂⟩ := exists_curve_double (s:=16) (v:=4) (d:=k-1) dom (u 0) (u 1)
    (by omega : 0<t₀) (by decide) (by rw [hn];exact double_capacity hdouble)
  let A := surface c₂
  have hA : A ≠ 0 := surface_ne_zero hc₂
  have ashape {j i a : ℕ} (h : ((A.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 4 ∧ i+j ≤ 16 ∧ a+j*(k-1)<2*t₀ := surface_support c₂ h
  have aval : A.natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (ashape h).1
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have shape {j i a : ℕ} (h : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 2 ∧ i+j ≤ s ∧ a+j*(k-1) < t₀ := surface_support c h
  have scalar (j : ℕ) : (Q.coeff j).natDegree ≤ s := by
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
      (hmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  have rootsAux (z : F) (hz : z ∈ fam.G) :
      A.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0 := by
    simp only [A,φ, Polynomial.map_id, RingHom.id_apply, surface_eval]
    apply witness₂ _ _ (by have := fam.degree_lt z hz; omega) (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (hmin.trans (ht ▸ fam.threshold_le z hz))
    exact fun i hi => (mem_filter.mp hi).2
  obtain ⟨P,E,hP,prim,hPQ,hval,_,hE,after⟩ := SecondPrimePrimitiveSurface.primitive_surface
    φ hQ fam.G (fun z => (fam.q z).map φ) s scalar roots
  obtain ⟨U, factors, _, hnum, hits⟩ := SecondPrimePrimitiveSurface.factor_cover P hP prim
  let V := U.toFinset
  have hV : V.card ≤ 2 := U.toFinset_card_le.trans (hnum.trans (hval.le.trans val))
  have cover (z : F) (hz : z ∈ fam.G) (he : z ∉ E) : ∃ f ∈ V, z ∈ pop f := by
    obtain ⟨f, hf, hroot⟩ := hits _ _ (after z hz he)
    exact ⟨f, Multiset.mem_toFinset.mpr hf, mem_filter.mpr ⟨hz,hroot⟩⟩
  let zmin := t - n/L
  apply TwoLargeCoreCount.card_le_two_mul_add_two fam (zmin := zmin) hk (by omega)
    (hn.trans hsum.symm) ht (by rw [hn]; exact geom)
  intro H hH hsize
  have some_large : ∃ f ∈ V, L < (H ∩ pop f).card := by
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
    have boundVL := Nat.mul_le_mul_right L hV
    omega
  obtain ⟨f,hf,hbig⟩ := some_large
  obtain ⟨hirr,hpos,hdiv⟩ := factors f (Multiset.mem_toFinset.mp hf)
  have hdivQ := hdiv.trans hPQ
  have hd := (natDegree_le_of_dvd hdivQ hQ).trans val
  have hpop : L < (pop f).card := hbig.trans_le (card_le_card inter_subset_right)
  have tri := SecondPrimeSectionResultant.factor_triangle hQ hdivQ (fun _ _ _ h => (shape h).2.1)
  have auxTri := SecondPrimeSectionResultant.factor_triangle hA dvd_rfl (fun _ _ _ h => (ashape h).2.1)
  have divAux : f ∣ A := by
    apply SecondPrimeSectionResultant.divides_of_many_sections φ f A hirr hpos tri auxTri (pop f)
      (fun z => (fam.q z).map φ) (fun z hz => ⟨(mem_filter.mp hz).2,rootsAux z (mem_filter.mp hz).1⟩)
    have m1 := Nat.mul_le_mul_right 16 hd
    have m2 := Nat.mul_le_mul_right s aval
    omega
  have htot := factor_totalDegree_le hA divAux (fun _ _ _ h => ((ashape h).2.1).trans (by decide : 16 ≤ 34))
  have triAux := SecondPrimeSectionResultant.factor_triangle hA divAux (fun _ _ _ h => (ashape h).2.1)
  have weightQ : SecondPrimeCoordinateWeight.weight (k-1) Q ≤ t₀-1 :=
    SecondPrimeCoordinateWeight.weight_le_of_coeff _ _ (fun j i a h => by have := (shape h).2.2;omega)
  have weightf : SecondPrimeCoordinateWeight.weight (k-1) f ≤ t₀-1 := by
    obtain ⟨g,hg⟩ := hdivQ
    rw [hg] at hQ weightQ
    rw [SecondPrimeCoordinateWeight.weight_mul _ f g (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at weightQ
    omega
  have commonShape (j i a : ℕ) (h : ((f.coeff j).coeff i).coeff a ≠ 0) : i+j ≤ 34 ∧ a ≤ t₀-1 := by
    have hj : f.coeff j ≠ 0 := fun eq => h (by simp [eq])
    have hi : (f.coeff j).coeff i ≠ 0 := fun eq => h (by simp [eq])
    have one := triAux j hj
    have two := le_natDegree_of_ne_zero hi
    have three := (SecondPrimeCoordinateWeight.coeff_weight_le (k-1) f h).trans weightf
    omega
  have hlin : f.natDegree = 1 := by
    by_contra hnon
    have hquad : f.natDegree=2 := by omega
    have bound := SecondPrimeQuadraticFactor.quadratic_population_of_extraction
      (w:=t₀-1) (m:=511) fam φ f f hirr.ne_zero dvd_rfl hirr hquad commonShape (by omega) hchar extract
    rw [population_eq f] at bound
    omega
  obtain ⟨p,hp,hcarry⟩ := linear_factor_is_head_of_extraction (m := 511) fam φ f hirr hlin
    htot extract (by rw [population_eq f]; omega)
  rw [population_eq f] at hcarry
  have hcar : H ∩ pop f ⊆ pointsOn fam p := inter_subset_right.trans hcarry
  have hcount : L ≤ (pointsOn fam p).card := hbig.le.trans (card_le_card hcar)
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < (H ∩ pop f).card by omega)
  refine ⟨a,(mem_inter.mp ha).1,b,(mem_inter.mp hb).1,hab,?_⟩
  rw [secantParameter_eq_of_mem_pointsOn fam p (hcar ha) (hcar hb) hab]
  have pack := pointsOn_card_mul_max_add_core_le fam hp
  rw [ht,hn] at pack
  let core := (jointCore dom (u 0) (u 1) p.1 p.2).card
  have packed : L * (t-core) ≤ n :=
    (Nat.mul_le_mul hcount (le_max_right 1 (t-core))).trans (by exact (Nat.le_add_right _ _).trans pack)
  have quotient : t-core ≤ n/L := (Nat.le_div_iff_mul_le (by omega)).mpr (mul_comm L _ ▸ packed)
  change t - n/L ≤ core
  omega

end ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount
#print axioms ArkLib.ProximityGap.Frontier.DoubleQuadraticHeadCount.family_cap
