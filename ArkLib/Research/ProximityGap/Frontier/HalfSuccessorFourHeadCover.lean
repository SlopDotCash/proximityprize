/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ScalarRegularJetSurface
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorNonlinearPopulation
import ArkLib.Research.ProximityGap.Frontier.HalfRateLinearPopulation
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount

/-! # Four actual collinear secants at the first half-rate successor -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.HalfSuccessorFourHeadCover
open SecondPrimeQuarticInterpolation SecondPrimePrimitiveSurface HalfSuccessorJetInterpolation
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines
open SecondPrimeCoordinateWeight
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}
private abbrev Family (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I) :=
  BadScalarRichPointFamily dom 536870912 δ u
private abbrev Poly (F : Type) [Field F] := F[X][X][X]

/-- Any actual population larger than the block length is covered, without exceptional
scalars, by four distinct secants, each carrying at least 268435451 actual labels. -/
theorem cover {p : ℕ} [CharP F p] (hp : 116 < p) (fam : Family dom δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (hbig : 1073741824 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H ⊆ lineParameters fam ∧ H.card = 4 ∧
      fam.G ⊆ H.biUnion (pointsOn fam) ∧ ∀ L ∈ H, 268435451 ≤ (pointsOn fam L).card := by
  classical
  obtain ⟨c,hc,hjets,_⟩ := production dom (u 0) (u 1) hn
  obtain ⟨s,b,hs,hb,hjb,hreg⟩ := ScalarRegularJetSurface.normalize dom (u 0) (u 1) (by decide) c hc hjets
  let Q := surface b
  have hQ : Q ≠ 0 := surface_ne_zero hb
  have htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 14 :=
    fun _ _ _ h => (surface_support b h).2.1.trans hs
  have hvalue : Q.natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support b h).1
  have hweight : weight 536870911 Q ≤ 2415919100 := weight_le_of_coeff _ _ (fun j i a h => by
    have := (surface_support b h).2.2; omega)
  have hsec (z : F) (hz : z ∈ fam.G) : Q.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    rw [show Q=surface b from rfl,surface_eval]
    apply rich_of_jets dom (u 0) (u 1) (by decide) (by decide) b hjb z (fam.q z)
      (by have := fam.degree_lt z hz; omega) (fullAgreement dom (u 0) (u 1) z (fam.q z))
      (by have := fam.threshold_le z hz; omega)
    exact fun i hi => (mem_filter.mp hi).2
  have hprim (z : F) (hz : z ∈ fam.G) : Q.primPart.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    have hnz : Q.content.eval (C z) ≠ 0 := by
      intro he
      apply hreg z
      change Q.map _ = 0
      conv_lhs => rw [eq_C_content_mul_primPart Q]
      rw [Polynomial.map_mul,map_C,coe_evalRingHom,he,map_zero,zero_mul]
    have hr := hsec z hz
    conv_lhs at hr => rw [eq_C_content_mul_primPart Q]
    rw [eval₂_mul,eval₂_C] at hr
    exact (mul_eq_zero.mp hr).resolve_left hnz
  obtain ⟨U,hU,_,hUc,hcov⟩ := factor_cover Q.primPart (primPart_ne_zero _) (isPrimitive_primPart _)
  rw [natDegree_primPart] at hUc
  let P (f : Poly F) := fam.G.filter fun z => f.eval₂ (evalRingHom (C z)) (fam.q z) = 0
  let A := U.toFinset.filter fun f => f.natDegree=1 ∧ 636 ≤ (P f).card
  let B := U.toFinset \ A
  have small (f) (hf : f ∈ B) : (P f).card ≤ 7572 := by
    obtain ⟨hfU,hfA⟩ := mem_sdiff.mp hf
    obtain ⟨hi,hpos,hdiv⟩ := hU f (Multiset.mem_toFinset.mp hfU)
    by_cases hlinear : f.natDegree=1
    · by_contra! he
      exact hfA (mem_filter.mpr ⟨hfU,hlinear,by omega⟩)
    have hd := hdiv.trans (primPart_dvd Q)
    have hm := SecondPrimeSectionResultant.factor_triangle hQ hd htri
    have hv := (natDegree_le_of_dvd hd hQ).trans hvalue
    have hw : weight 536870911 f ≤ 2415919100 := by
      obtain ⟨g,hg⟩ := hd
      have hg' : g ≠ 0 := fun e => hQ (by simp [hg,e])
      rw [hg,weight_mul _ _ _ hi.ne_zero hg'] at hweight
      omega
    have h := HalfSuccessorNonlinearPopulation.actual_population hp dom δ u hn ht.ge fam f hi
      (by omega) hv hm hw (P f) (filter_subset ..) (fun z hz => (mem_filter.mp hz).2)
    omega
  have secant (f : A) : ∃ L ∈ lineParameters fam, P f ⊆ pointsOn fam L := by
    obtain ⟨hfU,hlin,hbig'⟩ := mem_filter.mp f.property
    obtain ⟨hi,_,hdiv⟩ := hU f.val (Multiset.mem_toFinset.mp hfU)
    have hm := SecondPrimeSectionResultant.factor_triangle hQ (hdiv.trans (primPart_dvd Q)) htri
    apply HalfRateLinearPopulation.secant (RingHom.id F) fam hn (by omega) f hi hlin
      (fun j hj => (hm j hj).trans (by decide)) (P f) (filter_subset ..) hbig'
    simp [P]
  choose line hline hmem using secant
  let H := univ.image line
  have hH : H ⊆ lineParameters fam := by
    intro l hl
    obtain ⟨f,_,rfl⟩ := mem_image.mp hl
    exact hline f
  have cover' : fam.G ⊆ H.biUnion (pointsOn fam) ∪ B.biUnion P := by
    intro z hz
    obtain ⟨f,hf,hr⟩ := hcov z _ (hprim z hz)
    have hzP : z ∈ P f := mem_filter.mpr ⟨hz,hr⟩
    by_cases hfA : f∈A
    · exact mem_union_left _ (mem_biUnion.mpr ⟨line ⟨f,hfA⟩,mem_image_of_mem _ (mem_univ _),
        hmem ⟨f,hfA⟩ hzP⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨f,mem_sdiff.mpr ⟨Multiset.mem_toFinset.mpr hf,hfA⟩,hzP⟩)
  have occ (L : LineParameter F) (hL : L∈H) : (pointsOn fam L).card ≤ 268435458 :=
    TwoLargeCoreCount.line_occupancy_le fam (e:=268435457) hn ht (hH hL)
  have hocc := sum_le_sum (s:=H) (fun l hl => occ l hl)
  simp only [sum_const,smul_eq_mul] at hocc
  have hsm := sum_le_sum (s:=B) (fun f hf => small f hf)
  simp only [sum_const,smul_eq_mul] at hsm
  have hmass := (card_le_card cover').trans ((card_union_le ..).trans
    (Nat.add_le_add (card_biUnion_le.trans hocc) (card_biUnion_le.trans hsm)))
  have hB := card_le_card (s:=B) (t:=U.toFinset) sdiff_subset
  have hA := card_le_card (s:=A) (t:=U.toFinset) (filter_subset ..)
  have hLH : H.card ≤ A.card := card_image_le.trans (by simp)
  have hu := U.toFinset_card_le
  have hfour : H.card=4 := by omega
  have hAE : A = U.toFinset := eq_of_subset_of_card_le (filter_subset ..) (by omega)
  have hall : fam.G ⊆ H.biUnion (pointsOn fam) := by simpa [B,hAE] using cover'
  refine ⟨H,hH,hfour,hall,?_⟩
  intro L hL
  have hrest := sum_le_sum (s:=H.erase L) (fun l hl => occ l (mem_of_mem_erase hl))
  rw [sum_const,smul_eq_mul,card_erase_of_mem hL,hfour] at hrest
  have hsum := sum_erase_add H (fun l => (pointsOn fam l).card) hL
  have htot := (card_le_card hall).trans card_biUnion_le
  omega

#print axioms cover
end ArkLib.ProximityGap.Frontier.HalfSuccessorFourHeadCover
