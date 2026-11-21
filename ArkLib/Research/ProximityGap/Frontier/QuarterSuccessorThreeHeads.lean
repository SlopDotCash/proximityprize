/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorNonlinearPopulation
import ArkLib.Research.ProximityGap.Frontier.QuarterRateDoubleInterpolation

/-! # An over-budget quarter-rate successor requires three actual rich affine heads -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorThreeHeads
open Polynomial Finset Code SecondPrimeQuarticInterpolation SecondPrimeCoordinateWeight
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry
open _root_.ProximityGap.SecondPrimeLinearFactor
open scoped NNReal

private theorem trio {A B C : Type*} [DecidableEq A]
    (G E : Finset A) (V : Finset B) (pop : B → Finset A) (pts : C → Finset A)
    (valid : C → Prop) (hG : 1073741824 < G.card)
    (hE : E.card ≤ 16) (hV : V.card ≤ 3) (cover : G ⊆ E ∪ V.biUnion pop)
    (cap : ∀ h, valid h → (pts h).card ≤ 447392429)
    (extract : ∀ f ∈ V, 60143 < (pop f).card → ∃ h, valid h ∧ pop f ⊆ pts h) :
    ∃ H : Finset C, H.card = 3 ∧ G ⊆ E ∪ H.biUnion pts ∧
      ∀ h ∈ H, valid h ∧ 178956951 ≤ (pts h).card := by
  classical
  let L := V.filter fun f => 60143 < (pop f).card
  have lift (f : L) := extract f (mem_filter.mp f.property).1 (mem_filter.mp f.property).2
  choose line hline hcarry using lift
  let H := univ.image line
  let S := V \ L
  have small : ∀ f ∈ S, (pop f).card ≤ 60143 := by
    intro f hf
    exact not_lt.mp fun hh => (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨(mem_sdiff.mp hf).1, hh⟩)
  have hSmall := (card_biUnion_le (s := S) (t := pop)).trans (sum_le_sum small)
  simp only [sum_const, smul_eq_mul] at hSmall
  have val : ∀ h ∈ H, valid h := by
    intro h hh
    obtain ⟨f, _, rfl⟩ := mem_image.mp hh
    exact hline f
  have headCap (J : Finset C) (hJ : J ⊆ H) : (J.biUnion pts).card ≤ J.card * 447392429 :=
    card_biUnion_le.trans ((sum_le_sum (fun j hj => cap j (val j (hJ hj)))).trans_eq (by simp))
  have pushed : G ⊆ E ∪ (H.biUnion pts ∪ S.biUnion pop) := by
    intro z hz
    rcases mem_union.mp (cover hz) with he | h
    · exact mem_union_left _ he
    obtain ⟨f, hf, hz⟩ := mem_biUnion.mp h
    by_cases hfL : f ∈ L
    · let i : L := ⟨f, hfL⟩
      exact mem_union_right _ (mem_union_left _ (mem_biUnion.mpr
        ⟨line i, mem_image.mpr ⟨i, mem_univ _, rfl⟩, hcarry i hz⟩))
    · exact mem_union_right _ (mem_union_right _ (mem_biUnion.mpr
        ⟨f, mem_sdiff.mpr ⟨hf,hfL⟩, hz⟩))
  have size := (card_le_card pushed).trans
    ((card_union_le ..).trans (Nat.add_le_add_left (card_union_le ..) _))
  have lim := headCap H (Subset.rfl)
  have hHL : H.card ≤ L.card := by simpa only [H, card_univ, Fintype.card_coe] using
      (card_image_le (s := (univ : Finset L)) (f := line))
  have hLV : L ⊆ V := filter_subset ..
  have hLVcard := card_le_card hLV
  have hS : S.card = V.card - L.card := card_sdiff_of_subset hLV
  have eqH : H.card = 3 := by omega
  have empty : S = ∅ := card_eq_zero.mp (by omega)
  have hcov : G ⊆ E ∪ H.biUnion pts := by
    simpa [empty] using pushed
  refine ⟨H, eqH, hcov, fun h hh => ⟨val h hh, ?_⟩⟩
  have two := headCap (H.erase h) (erase_subset ..)
  rw [card_erase_of_mem hh, eqH] at two
  have rem : H.biUnion pts = pts h ∪ (H.erase h).biUnion pts := by
    conv_lhs => rw [← insert_erase hh]
    rw [biUnion_insert]
  have budget := (card_le_card hcov).trans (card_union_le ..)
  rw [rem] at budget
  have split := card_union_le (pts h) ((H.erase h).biUnion pts)
  omega

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Finite F]
variable [DecidableEq F] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Any genuine over-budget family admits a three-secant cover up to sixteen exceptional
scalars. Each of the three distinct secants has at least 178956951 genuine labels. -/
theorem actual_heads {p : ℕ} [CharP F p] (hp : 132 < p)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396) (hG : 1073741824 < fam.G.card) :
    ∃ (E : Finset F) (H : Finset (LineParameter F)),
      E.card ≤ 16 ∧ H.card = 3 ∧ fam.G ⊆ E ∪ H.biUnion (pointsOn fam) ∧
        ∀ h ∈ H, h ∈ lineParameters fam ∧ 178956951 ≤ (pointsOn fam h).card := by
  classical
  let _ := Fintype.ofFinite F
  have extract : SecantExtraction fam 512 := by
    intro M hM hm U
    apply extraction_of_geometry (m := 478) (t := 626349396) fam (by decide) (by decide)
      _ M hM hm U hn ht.ge
    intro c a b l v hc hinc hcover ha hb hl
    omega
  have capacity : 1073741824 * 50 < Fintype.card (Monomials 16 3 268435455 (2 * 626349396)) := by
    simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    norm_num [Fin.sum_univ_succ]
  obtain ⟨c, hc, fits⟩ := exists_curve_double (s := 16) (v := 3) (d := 268435455) dom
    (u 0) (u 1) (by decide : 0 < 626349396) (by decide) (by rw [hn]; exact capacity)
  let Q := surface c
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have shape {j i a : ℕ} (hx : ((Q.coeff j).coeff i).coeff a ≠ 0) :
      j ≤ 3 ∧ i + j ≤ 16 ∧ a + j * 268435455 < 2 * 626349396 := surface_support c hx
  have hval : Q.natDegree ≤ 3 :=
    (shape (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hQ)))).1
  have scalar (j : ℕ) : (Q.coeff j).natDegree ≤ 16 := by
    by_cases hz : Q.coeff j = 0
    · simp [hz]
    have k := shape (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hz))
    omega
  have root (z : F) (hz : z ∈ fam.G) : Q.eval₂ (evalRingHom (C z)) (fam.q z) = 0 := by
    have hh := fits z (fam.q z) (by have := fam.degree_lt z hz; omega)
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) (ht ▸ fam.threshold_le z hz)
      (fun i hi => (mem_filter.mp hi).2)
    simpa only [Q, surface_eval] using hh
  obtain ⟨P,E,hP,hprim,hPQ,hv,_,hE,after⟩ :=
    SecondPrimePrimitiveSurface.primitive_surface (RingHom.id F) hQ fam.G fam.q 16 scalar root
  obtain ⟨U, factors, _, hnum, hits⟩ := SecondPrimePrimitiveSurface.factor_cover P hP hprim
  let V := U.toFinset
  let pop (f : F[X][X][X]) := fam.G.filter fun z => f.eval₂ (evalRingHom (C z)) (fam.q z) = 0
  have info (f) (hf : f ∈ V) := factors f (Multiset.mem_toFinset.mp hf)
  have cover : fam.G ⊆ E ∪ V.biUnion pop := by
    intro z hz
    by_cases he : z ∈ E
    · exact mem_union_left _ he
    obtain ⟨f,hf,hr⟩ := hits _ _ (after z hz he)
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨f, Multiset.mem_toFinset.mpr hf, mem_filter.mpr ⟨hz, hr⟩⟩)
  have carries (f) (hf : f ∈ V) (hbig : 60143 < (pop f).card) :
      ∃ a, a ∈ lineParameters fam ∧ pop f ⊆ pointsOn fam a := by
    obtain ⟨irr, pos, divides⟩ := info f hf
    have hd := divides.trans hPQ
    have tri := SecondPrimeSectionResultant.factor_triangle hQ hd (fun _ _ _ h => (shape h).2.1)
    have hdeg : f.natDegree ≤ 3 := (natDegree_le_of_dvd hd hQ).trans hval
    have hwQ := weight_le_of_coeff 268435455 Q (W := 1252698791) (fun _ _ _ h => by
      have := (shape h).2.2
      omega)
    have hw : weight 268435455 f ≤ 1252698791 := by
      obtain ⟨r, hh⟩ := hd
      have hr : r ≠ 0 := by intro hr; simp [hh, hr] at hQ
      rw [hh, weight_mul _ _ _ irr.ne_zero hr] at hwQ
      omega
    have one : f.natDegree = 1 := by
      by_contra h
      have bound := QuarterSuccessorNonlinearPopulation.actual_population hp dom δ u hn ht.ge fam f
        irr (by omega) hdeg tri hw (pop f) (filter_subset ..) (fun z hz => (mem_filter.mp hz).2)
      omega
    have htD := factor_totalDegree_le hQ hd (fun _ _ _ h => ((shape h).2.1).trans (by decide))
    have lift := linear_factor_is_head_of_extraction (m := 511) fam (RingHom.id F) f irr one
      htD extract
    simpa only [RingHom.id_apply, Polynomial.map_id] using
      lift (by simpa only [RingHom.id_apply, Polynomial.map_id] using
        (show 511 < (pop f).card by omega))
  obtain ⟨H, HH⟩ := trio fam.G E V pop (pointsOn fam) (fun h => h ∈ lineParameters fam)
    hG hE (U.toFinset_card_le.trans (hnum.trans (hv.le.trans hval))) cover
    (fun h hh => TwoLargeCoreCount.line_occupancy_le fam (e := 447392428) (t := 626349396)
      hn ht hh) carries
  exact ⟨E, H, hE, HH⟩

end ArkLib.ProximityGap.Frontier.QuarterSuccessorThreeHeads
