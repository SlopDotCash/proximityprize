/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateQuadraticSafety
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant

/-! # Two quarter-rate interpolants and the forced pair of large secants -/

namespace ArkLib.ProximityGap.Frontier.QuarterRateDoubleInterpolation
open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open _root_.ProximityGap _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private abbrev d := 268435455
private abbrev s := 268435458
private abbrev t₀ := 626349397
private abbrev n := 1073741824

private theorem simple_capacity : n*(s+1) < Fintype.card (Monomials s 2 d t₀) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ,n,s,d,t₀]

private theorem double_capacity : n*50 < Fintype.card (Monomials 16 3 d (2*t₀)) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ,n,d,t₀]

omit [Fintype F] in
private theorem value_bound {h v t : ℕ} (c : Monomials h v d t → F) :
    (surface c).natDegree ≤ v := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext i a
  simp only [coeff_zero]
  by_contra h
  exact hj.not_ge (surface_support c h).1

/-- An overfull family in the terminal two-head region forces two distinct
secants above the requested population cutoff. -/
theorem asymmetric_heavy_pair (fam : BadScalarRichPointFamily dom 268435456 δ u)
    {e t L M : ℕ} (hn : Fintype.card I=n) (hsum : e+t=n) (hmin : t₀ ≤ t)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0)
    (hL : 511 ≤ L) (hLM : L ≤ M) (hcubic : 805306416 < fam.G.card)
    (hmax : 16+3*M < fam.G.card)
    (hbig : 16+(e+1)+2*L < fam.G.card) :
    ∃ a ∈ lineParameters fam, ∃ b ∈ lineParameters fam,
      a ≠ b ∧ M < (pointsOn fam a).card ∧ L < (pointsOn fam b).card := by
  classical
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m:=478) (t:=t₀) fam (by decide) (by decide)
      _ M hM hm U hn (hmin.trans ht.ge)
    intro c a b l v hc hinc hcover ha hb hl
    dsimp only [n,t₀] at *
    omega
  obtain ⟨c₁,hc₁,_,hw₁⟩ := exists_curve (s:=s) (v:=2) (d:=d) dom (u 0) (u 1)
    (by decide : 0 < t₀) (by rw [hn];exact simple_capacity)
  obtain ⟨c₂,hc₂,hw₂⟩ := exists_curve_double (s:=16) (v:=3) (d:=d) dom (u 0) (u 1)
    (by decide : 0 < t₀) (by decide) (by rw [hn];exact double_capacity)
  let Q := surface c₂
  let R := surface c₁
  have hQ : Q ≠ 0 := surface_ne_zero hc₂
  have hR : R ≠ 0 := surface_ne_zero hc₁
  have shape {j i a : ℕ} (hz : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 3 ∧ i+j ≤ 16 ∧ a+j*d < 2*t₀ := surface_support c₂ hz
  have scalar (j : ℕ) : (Q.coeff j).natDegree ≤ 16 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext a
    simp only [coeff_zero]
    by_contra h
    have := (shape h).2.1
    omega
  let φ := RingHom.id F
  let w (z : F) := (fam.q z).map φ
  let pop (f : F[X][X][X]) := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) (w z)=0
  have peq (f : F[X][X][X]) (D : DecidablePred fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ)=0) :
      @Finset.filter F _ D fam.G = pop f := by ext z; simp only [pop,w,mem_filter]
  have roots (z:F) (hz:z ∈ fam.G) : Q.eval₂ (evalRingHom (C (φ z))) (w z)=0 ∧
      R.eval₂ (evalRingHom (C (φ z))) (w z)=0 := by
    have degree : (fam.q z).natDegree ≤ d := by have := fam.degree_lt z hz; dsimp [d]; omega
    have card := hmin.trans (ht ▸ fam.threshold_le z hz)
    have fits (i : I) (hi : i ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)) := (mem_filter.mp hi).2
    simpa only [Q,R,w,φ,RingHom.id_apply,Polynomial.map_id,surface_eval] using
      And.intro (hw₂ z _ degree _ card fits) (hw₁ z _ degree _ card fits)
  obtain ⟨P,E,hP,prim,hPQ,hval,_,hE,after⟩ :=
    SecondPrimePrimitiveSurface.primitive_surface φ hQ fam.G w 16 scalar (fun z hz => (roots z hz).1)
  obtain ⟨U,factors,hs,hnum,hits⟩ := SecondPrimePrimitiveSurface.factor_cover P hP prim
  let V := U.toFinset
  have hV : V.card ≤ 3 := U.toFinset_card_le.trans (hnum.trans (hval.le.trans (value_bound c₂)))
  have cover : fam.G ⊆ E ∪ V.biUnion pop := by
    intro z hz
    by_cases ze : z ∈ E
    · exact mem_union_left _ ze
    · obtain ⟨f,hf,hr⟩ := hits _ _ (after z hz ze)
      exact mem_union_right _ (mem_biUnion.mpr ⟨f,Multiset.mem_toFinset.mpr hf,mem_filter.mpr ⟨hz,hr⟩⟩)
  have info (f) (hf : f ∈ V) := factors f (Multiset.mem_toFinset.mp hf)
  have tot (f) (hf : f ∈ V) := SecondPrimeSectionResultant.factor_triangle hQ ((info f hf).2.2.trans hPQ)
    (fun _ _ _ h => (shape h).2.1)
  have hsumD : ∑ f ∈ V,f.natDegree ≤ 3 := by
    obtain ⟨T,hT⟩ := exists_add_of_le (Multiset.dedup_le U)
    change (U.toFinset.val.map Polynomial.natDegree).sum ≤ 3
    rw [Multiset.toFinset_val]
    rw [hT,Multiset.map_add,Multiset.sum_add] at hs
    have hv := hval.le.trans (value_bound c₂)
    omega
  have no_cubic (f) (hf : f ∈ V) : f.natDegree ≤ 2 := by
    by_contra! more
    have hy : f.natDegree=3 := by
      have := (natDegree_le_of_dvd ((info f hf).2.2.trans hPQ) hQ).trans (value_bound c₂)
      omega
    have only : V={f} := by
      have sum := sum_erase_add (s:=V) Polynomial.natDegree hf
      have hs₁ : (V.erase f).card ≤ ∑ a ∈ V.erase f,a.natDegree := by
        simpa using (sum_le_sum (s:=V.erase f) fun a ha => (show 1 ≤ a.natDegree from (info a (mem_of_mem_erase ha)).2.1))
      have hz : V.erase f=∅ := card_eq_zero.mp (by omega)
      simpa [hz] using (insert_erase hf).symm
    have hle := SecondPrimeSectionResultant.cubic_section_cap φ f R (info f hf).1 hy hR
      (value_bound c₁) (m:=16) (s:=s) (by decide) (tot f hf)
      (SecondPrimeSectionResultant.factor_triangle hR dvd_rfl (fun _ _ _ h => (surface_support c₁ h).2.1))
      (pop f) w (fun z hz => ⟨(mem_filter.mp hz).2,(roots z (mem_filter.mp hz).1).2⟩)
    have hcov := card_le_card cover
    rw [only, singleton_biUnion] at hcov
    have := hcov.trans (card_union_le ..)
    dsimp only [s] at hle
    omega
  let large := V.filter fun f => L < (pop f).card
  have head (f : large) : ∃ a ∈ lineParameters fam, pop f ⊆ pointsOn fam a := by
    obtain ⟨hf,hpop⟩ := mem_filter.mp f.property
    have hd := no_cubic f hf
    have fi := info f hf
    have hv := factor_totalDegree_le hQ (fi.2.2.trans hPQ) (fun _ _ _ h => by have := (shape h).2.1;omega)
    have linear : f.val.natDegree=1 := by
      by_contra non
      have hh := SecondPrimeQuadraticFactor.quadratic_population_weighted (m:=511) (w:=1252698793) (d:=268435455)
        fam φ Q f hQ (fi.2.2.trans hPQ) fi.1 (by omega) (fun j i a h => by
          have := shape h
          dsimp [d,t₀] at this
          exact ⟨by omega,by omega⟩) (by decide) (by decide) hchar extract
      rw [peq f] at hh
      omega
    obtain ⟨a,ha,hs⟩ := linear_factor_is_head_of_extraction (m:=511) fam φ f fi.1 linear hv extract (by rw [peq f];omega)
    rw [peq f] at hs
    exact ⟨a,ha,hs⟩
  choose line valid contains using head
  have occ (i : large) : L < (pointsOn fam (line i)).card :=
    (mem_filter.mp i.property).2.trans_le (card_le_card (contains i))
  have some_heavy : ∃ i : large, M < (pointsOn fam (line i)).card := by
    by_contra! cut
    have pop_le (f) (hf : f ∈ V) : (pop f).card ≤ M := by
      by_cases h : f ∈ large
      · exact (card_le_card (contains ⟨f,h⟩)).trans (cut ⟨f,h⟩)
      · exact (not_lt.mp (fun hb => h (mem_filter.mpr ⟨hf,hb⟩))).trans hLM
    have bound : (V.biUnion pop).card ≤ V.card*M :=
      card_biUnion_le.trans ((sum_le_sum pop_le).trans_eq (by simp))
    have count := (card_le_card cover).trans (card_union_le ..)
    have cap := Nat.mul_le_mul_right M hV
    omega
  obtain ⟨i,first⟩ := some_heavy
  let a := line i
  by_contra! bad
  let small := V \ large
  have small_factor (f) (hf : f ∈ small) : (pop f).card ≤ L := by
    exact not_lt.mp (fun h => (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨(mem_sdiff.mp hf).1,h⟩))
  have hsmall : (small.biUnion pop).card ≤ small.card*L :=
    card_biUnion_le.trans ((sum_le_sum small_factor).trans_eq (by simp))
  have eq (j : large) : line j=a := by
    by_contra ne
    exact (bad _ (valid i) _ (valid j) (Ne.symm ne) first).not_gt (occ j)
  have hsub : fam.G ⊆ E ∪ ((pointsOn fam a) ∪ small.biUnion pop) := by
    intro z hz
    rcases mem_union.mp (cover hz) with he | hh
    · exact mem_union_left _ he
    obtain ⟨g,hg,hz⟩ := mem_biUnion.mp hh
    by_cases hl : g ∈ large
    · exact mem_union_right _ (mem_union_left _ (eq ⟨g,hl⟩ ▸ contains ⟨g,hl⟩ hz))
    · exact mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨g,mem_sdiff.mpr ⟨hg,hl⟩,hz⟩))
  have ac := TwoLargeCoreCount.line_occupancy_le fam (hn.trans hsum.symm) ht (valid i)
  have sc := card_sdiff_of_subset (show large ⊆ V from filter_subset ..)
  have pc : 1 ≤ large.card := card_pos.mpr ⟨i.val,i.property⟩
  have sm : small.card ≤ 2 := by dsimp [small];omega
  have budget := Nat.mul_le_mul_right L sm
  have hcount := (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left (card_union_le ..) _))
  change (pointsOn fam a).card ≤ e+1 at ac
  omega

/-- An overfull family in the terminal two-head region forces two distinct
secants above the requested population cutoff. -/
theorem heavy_pair (fam : BadScalarRichPointFamily dom 268435456 δ u)
    {e t L : ℕ} (hn : Fintype.card I=n) (hsum : e+t=n) (hmin : t₀ ≤ t)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=t)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ 1968526676 → (i:F) ≠ 0)
    (hL : 511 ≤ L) (hLe : L ≤ e+1) (hcubic : 805306416 < fam.G.card)
    (hbig : 16+(e+1)+2*L < fam.G.card) :
    ∃ a ∈ lineParameters fam, ∃ b ∈ lineParameters fam,
      a ≠ b ∧ L < (pointsOn fam a).card ∧ L < (pointsOn fam b).card := by
  exact asymmetric_heavy_pair fam hn hsum hmin ht hchar hL (le_refl L) hcubic (by omega) hbig

end ArkLib.ProximityGap.Frontier.QuarterRateDoubleInterpolation

#print axioms ArkLib.ProximityGap.Frontier.QuarterRateDoubleInterpolation.heavy_pair
