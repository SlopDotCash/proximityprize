/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Research.ProximityGap.Frontier.FlatSurfacePopulation
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface

/-! # Counting all bad scalars using an interpolant of arbitrary multiplicity

The input conditions involve only integer parameters. The bound applies to every
received pair on every injectively indexed domain of the stated cardinality.
-/

set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.JetSurfaceSafety
open SecondPrimeQuarticInterpolation SecondPrimeCoordinateWeight SecondPrimeSectionResultant
open HalfPredecessorLineCoreGeometry HalfPredecessorBadEventRichPointBridge HalfSuccessorJetInterpolation
variable {K I : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [Nonempty I] [DecidableEq I]

private theorem sum_distinct_le {A : Type} [DecidableEq A] (U : Multiset A) (D : A → ℕ) :
    ∑ f ∈ U.toFinset, D f ≤ (U.map D).sum := by
  change (U.dedup.map D).sum ≤ _
  obtain ⟨R,h⟩ := Multiset.le_iff_exists_add.mp (Multiset.dedup_le U)
  calc _ ≤ (U.dedup.map D).sum+(R.map D).sum := Nat.le_add_right _ _
       _ = _ := by conv_rhs => rw [h,Multiset.map_add,Multiset.sum_add]

/-- If the jet interpolation system has positive dimension, its primitive components
cover all bad scalars outside at most `m` vertical exceptions. The component costs
are charged against the total value degree `v`. -/
theorem bad_card_le {p : ℕ} [CharP K p] (hp : p.Prime) (dom : I ↪ K) (δ : ℝ≥0)
    (u : Code.WordStack K (Fin 2) I) (d t m v r C₀ : ℕ)
    (hr : 0 < r) (hrs : r ≤ m+1) (hdt : d < t) (htn : t ≤ Fintype.card I)
    (htag : t ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (hy : v ≤ m) (hm : 2 ≤ m) (hvp : v < p) (hdp : d < p) (hwp : r*t ≤ p)
    (hcount : Fintype.card I * Fintype.card (JetRows m r) <
      Fintype.card (Monomials m v d (r*t)))
    (hline : Fintype.card I ≤ C₀) (hflat : (Fintype.card I-d)*m ≤ C₀*(t-d))
    (htrans : ∀ b, 1 ≤ b → b ≤ v →
      let j := max 2 b
      j*(m+2*d*(m-1))+(j+2*d*(j-1))*m-j*(j+2*d*(j-1)) ≤ b*C₀) :
    (badScalars dom (d+1) δ u).card ≤ m+v*C₀ := by
  classical
  let fam := canonicalBadScalarRichPointFamily dom δ u (by omega : 1 ≤ d+1)
  obtain ⟨c,hc,_,hcurve⟩ := exists_surface dom (u 0) (u 1) hr (by omega : 0<t) hrs hcount
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have htQ := factor_triangle hQ dvd_rfl (fun j i a h => (surface_support c h).2.1)
  have hyQ : Q.natDegree ≤ v := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  have hdeg (j : ℕ) : (Q.coeff j).natDegree ≤ m := by
    by_cases hj : Q.coeff j=0
    · simp [hj]
    · have hh := htQ j hj; omega
  have hwQ : weight d Q ≤ r*t-1 := weight_le_of_coeff d Q (fun j i a h => by
    have hw := (surface_support c h).2.2
    omega)
  have hroot (z : K) (hz : z ∈ fam.G) : Q.eval₂ (evalRingHom (Polynomial.C z)) (fam.q z) = 0 := by
    apply (surface_eval c ..).trans
    exact hcurve z (fam.q z) (Nat.le_of_lt_succ (fam.degree_lt z hz))
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (htag.trans (fam.threshold_le z hz))
      (fun i hi => (mem_filter.mp hi).2)
  obtain ⟨P,E,hP,hprim,hPQ,hPy,_,hE,hPr⟩ :=
    SecondPrimePrimitiveSurface.primitive_surface (RingHom.id K) hQ fam.G fam.q m hdeg hroot
  obtain ⟨U,hU,hsum,_,hcover⟩ := SecondPrimePrimitiveSurface.factor_cover P hP hprim
  let M (f : Surface K) := fam.G.filter fun z => f.eval₂ (evalRingHom (Polynomial.C z)) (fam.q z)=0
  have hcov : fam.G ⊆ E ∪ U.toFinset.biUnion M := by
    intro z hz
    by_cases he : z ∈ E
    · exact mem_union_left _ he
    obtain ⟨f,hf,hfr⟩ := hcover z (fam.q z) (hPr z hz he)
    exact mem_union_right _ (mem_biUnion.mpr ⟨f,Multiset.mem_toFinset.mpr hf,mem_filter.mpr ⟨hz,hfr⟩⟩)
  have hcost (f : Surface K) (hf : f ∈ U.toFinset) : (M f).card ≤ f.natDegree*C₀ := by
    obtain ⟨hi,hpos,hfP⟩ := hU f (Multiset.mem_toFinset.mp hf)
    have hfQ := hfP.trans hPQ
    have hfv := (natDegree_le_of_dvd hfQ hQ).trans hyQ
    have htriangle := factor_triangle hQ hfQ (fun j i a h => (surface_support c h).2.1)
    have hweight : weight d f < p := by
      obtain ⟨g,hg⟩ := hfQ
      have hfg : f*g ≠ 0 := hg ▸ hQ
      rw [hg,weight_mul d f g hi.ne_zero (right_ne_zero_of_mul hfg)] at hwQ
      have := Nat.mul_pos hr (by omega : 0<t)
      omega
    rcases FlatSurfacePopulation.component_bound hp f hi hpos m (max 2 f.natDegree) d t
      (le_max_left ..) (max_le hm (hfv.trans hy)) htriangle (le_max_right ..)
      (hfv.trans_lt hvp) hdp hweight hdt htn dom δ u fam htag (M f) (filter_subset ..)
      (fun z hz => (mem_filter.mp hz).2) with flat | line | trans
    · exact (Nat.le_of_mul_le_mul_right (flat.trans hflat) (by omega)).trans
        (Nat.le_mul_of_pos_left _ hpos)
    · exact (line.trans hline).trans (Nat.le_mul_of_pos_left _ hpos)
    · exact trans.trans (htrans _ hpos hfv)
  have hmass : fam.G.card ≤ E.card+∑ f ∈ U.toFinset, (M f).card :=
    (card_le_card hcov).trans ((card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _))
  have hdU := (sum_distinct_le U natDegree).trans (hsum.trans_le (hPy.trans_le hyQ))
  have hM := sum_le_sum hcost
  rw [← sum_mul] at hM
  exact hmass.trans (Nat.add_le_add hE (hM.trans (Nat.mul_le_mul_right _ hdU)))

/-- Quarter rate at agreement `74/128`, including the exact endpoint. The second-order
system has 4,100 columns per unit of length scale before the degree-minus-one bonus,
and 4,096 equations per unit. -/
theorem quarter_54_card {p : ℕ} [CharP K p] (hp : p.Prime) (dom : I ↪ K) (δ : ℝ≥0)
    (u : Code.WordStack K (Fin 2) I) (a : ℕ) (ha : 0<a) (hn : Fintype.card I=128*a)
    (hchar : 148*a ≤ p) (htag : 74*a ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊) :
    (badScalars dom (32*a) δ u).card ≤ 6656*a-54 := by
  have hk : 32*a-1+1 = 32*a := by omega
  rw [← hk]
  have hh := bad_card_le hp dom δ u (32*a-1) (74*a) 10 4 2 (1664*a-16)
    (by decide) (by decide) (by omega) (by omega) htag (by decide) (by decide) (by omega)
    (by omega) (by omega) ?_ (by omega) ?_ ?_
  · omega
  · rw [hn]
    simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    norm_num [Fin.sum_univ_succ] <;> omega
  · have h₁ : 128*a-(32*a-1)=96*a+1 := by omega
    have h₂ : 74*a-(32*a-1)=42*a+1 := by omega
    rw [hn,h₁,h₂]
    calc (96*a+1)*10 ≤ (1664*a-16)*10 := by omega
         _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · intro b hb hv
    interval_cases b <;> norm_num <;> omega

/-- Worst-case probability of a bad scalar for quarter-rate Reed–Solomon on every
injective domain, throughout the full closed `54/128` error window. -/
theorem quarter_54_eps {p : ℕ} [CharP K p] (hp : p.Prime) (dom : I ↪ K) (δ : ℝ≥0)
    (a : ℕ) (ha : 0<a) (hn : Fintype.card I=128*a) (hchar : 148*a ≤ p)
    (htag : 74*a ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊) :
    _root_.ProximityGap.epsMCA (F:=K) (ReedSolomon.code dom (32*a) : Set (I → K)) δ ≤
      ((6656*a-54 : ℕ) : ℝ≥0∞)/(Fintype.card K : ℝ≥0∞) :=
  _root_.ProximityGap.epsMCA_le_of_badCount_le _ _ _ (fun u => quarter_54_card hp dom δ u a ha hn hchar htag)

#print axioms quarter_54_eps
#print axioms bad_card_le
end ArkLib.ProximityGap.Frontier.JetSurfaceSafety
