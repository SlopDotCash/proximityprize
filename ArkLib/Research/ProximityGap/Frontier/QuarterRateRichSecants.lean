/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateApolarBracket
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import ArkLib.Research.ProximityGap.Frontier._FSMB_CoreAbsorptionLadder
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # Fresh agreements of two rich secants with maximal overlap

At a saturated core intersection, every fresh agreement on the opposite core
contributes the same scalar label. Other labels consume distinct sites outside
both cores. The bound applies directly to families of bad folded witnesses.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateRichSecants
open Finset Polynomial Code
open HalfPredecessorLineCoreGeometry HalfPredecessorBadEventRichPointBridge
open HalfPredecessorSecantLines HalfPredecessorRateQuarterComplementaryCores
open scoped NNReal

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- At maximal overlap all but at most one of the first line's labels need
distinct fresh sites outside both cores. -/
theorem fresh_cap [Finite F] (D : I ↪ F) (u v : I → F) (a b c d : F[X]) (G : Finset F)
    (distinct : a ≠ c ∨ b ≠ d)
    (hdeg : max (a - c).natDegree (b - d).natDegree ≤
      (jointCore D u v a b ∩ jointCore D u v c d).card)
    (fresh : ∀ z ∈ G, ¬ fullAgreement D u v z (a + C z * b) ⊆ jointCore D u v a b) :
    G.card ≤ (univ \ (jointCore D u v a b ∪ jointCore D u v c d)).card + 1 := by
  classical
  let _ := Fintype.ofFinite F
  let A := jointCore D u v a b
  let B := jointCore D u v c d
  let sites := (A ∩ B).map D
  let R := univ \ (A ∪ B)
  let good (z : F) := fullAgreement D u v z (a + C z * b) \ A
  have hx (z : F) (hz : z ∈ G) : (good z).Nonempty := by
    obtain ⟨i, hi, ha⟩ := Finset.not_subset.mp (fresh z hz)
    exact ⟨i, mem_sdiff.mpr ⟨hi, ha⟩⟩
  let pick (z : F) : I := if h : z ∈ G then (hx z h).choose else Classical.ofNonempty
  have hpick {z : F} (hz : z ∈ G) : pick z ∈ good z := by
    simpa only [pick, dite_eq_left hz] using (hx z hz).choose_spec
  let L := G.filter (fun z => pick z ∈ B)
  have hp : a - c ≠ 0 ∨ b - d ≠ 0 := distinct.imp sub_ne_zero.mpr sub_ne_zero.mpr
  have hX : sites.card = (A ∩ B).card := card_map _
  have hl : L.card ≤ 1 := by
    apply QuarterRateApolarBracket.saturated_overlap (a-c) (b-d) sites L hp
    · rw [hX]
      exact (le_max_left ..).trans hdeg
    · rw [hX]
      exact (le_max_right ..).trans hdeg
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
      obtain ⟨hA, hB⟩ := mem_inter.mp hi
      have au := (mem_filter.mp hA).2
      have cu := (mem_filter.mp hB).2
      simp only [eval_sub, au.1, au.2, cu.1, cu.2, sub_self, and_self]
    · intro z hz
      obtain ⟨hg, hB⟩ := mem_filter.mp hz
      obtain ⟨hag, hA⟩ := mem_sdiff.mp (hpick hg)
      refine ⟨D (pick z), ?_, ?_⟩
      · intro h
        obtain ⟨i, hi, he⟩ := mem_map.mp h
        exact hA (D.injective he ▸ (mem_inter.mp hi).1)
      · have hc := (mem_filter.mp hB).2
        have ha := (mem_filter.mp hag).2
        simp only [eval_add, eval_mul, eval_C] at ha
        simp only [eval_sub, hc.1, hc.2]
        linear_combination ha
  have hrest : (G \ L).card ≤ R.card := by
    apply card_le_card_of_injOn pick
    · intro z hz
      obtain ⟨hg, hn⟩ := mem_sdiff.mp hz
      exact mem_sdiff.mpr ⟨mem_univ _, fun h => (mem_union.mp h).elim
        (mem_sdiff.mp (hpick hg)).2 (fun hB => hn (mem_filter.mpr ⟨hg, hB⟩))⟩
    · intro z hz w hw he
      by_contra hne
      have hd := freshAgreement_disjoint D u v a b hne
      exact Finset.disjoint_left.mp hd (hpick (mem_sdiff.mp hz).1)
        (he ▸ hpick (mem_sdiff.mp hw).1)
  have hsplit := card_sdiff_add_card_eq_card (filter_subset (fun z => pick z ∈ B) G)
  change (G \ L).card + L.card = G.card at hsplit
  change G.card ≤ R.card + 1
  omega

omit [DecidableEq I] [Nonempty I] in
/-- A simple interpolant and a double-root interpolant vanish simultaneously
on every actual folded witness at the target agreement. Their coefficient
spaces retain the scalar degrees needed for the resultant count. -/
theorem shared_equations {D : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily D 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : 626349397 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    ∃ (a : SecondPrimeQuarticInterpolation.Monomials 268435458 2 268435455 626349397 → F)
      (b : SecondPrimeQuarticInterpolation.Monomials 16 3 268435455 (2 * 626349397) → F),
      a ≠ 0 ∧ b ≠ 0 ∧ ∀ z ∈ fam.G,
        SecondPrimeQuarticInterpolation.specialize a z (fam.q z) = 0 ∧
        SecondPrimeQuarticInterpolation.specialize b z (fam.q z) = 0 := by
  classical
  have c₁ : 1073741824 * (268435458 + 1) <
      Fintype.card (SecondPrimeQuarticInterpolation.Monomials 268435458 2 268435455 626349397) := by
    simp only [SecondPrimeQuarticInterpolation.Monomials, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin]
    norm_num [Fin.sum_univ_succ]
  have c₂ : 1073741824 * (2 * (16 + 1) + 16) <
      Fintype.card (SecondPrimeQuarticInterpolation.Monomials 16 3 268435455 (2 * 626349397)) := by
    simp only [SecondPrimeQuarticInterpolation.Monomials, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin]
    norm_num [Fin.sum_univ_succ]
  obtain ⟨a, ha, _, va⟩ := SecondPrimeQuarticInterpolation.exists_curve
    (s := 268435458) (v := 2) (d := 268435455) D (u 0) (u 1)
    (by decide : 0 < 626349397) (by rw [hn]; exact c₁)
  obtain ⟨b, hb, vb⟩ := SecondPrimeQuarticInterpolation.exists_curve_double
    (s := 16) (v := 3) (d := 268435455) D (u 0) (u 1)
    (by decide : 0 < 626349397) (by decide) (by rw [hn]; exact c₂)
  refine ⟨a, b, ha, hb, ?_⟩
  intro z hz
  have hd : (fam.q z).natDegree ≤ 268435455 := by have := fam.degree_lt z hz; omega
  let S := fullAgreement D (u 0) (u 1) z (fam.q z)
  have hS : 626349397 ≤ S.card := ht.trans (fam.threshold_le z hz)
  have he (i : I) (hi : i ∈ S) := (mem_filter.mp hi).2
  exact ⟨va z _ hd S hS he, vb z _ hd S hS he⟩

omit [DecidableEq I] in
/-- Two rich distinct secants cannot occur in an over-budget family at the
quarter-rate predecessor. The argument only uses the actual received rows. -/
theorem two_rich_cap [Finite F] {D : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily D 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (a b : LineParameter F) (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
    (hab : a ≠ b) (ra : 223696215 ≤ (pointsOn fam a).card)
    (rb : 223696215 ≤ (pointsOn fam b).card) : fam.G.card ≤ 1073741824 := by
  classical
  let _ := Fintype.ofFinite F
  let K (l : LineParameter F) := jointCore D (u 0) (u 1) l.1 l.2
  have core (l : LineParameter F) (hl : l ∈ lineParameters fam)
      (hr : 223696215 ≤ (pointsOn fam l).card) : 626349396 ≤ (K l).card := by
    have h := pointsOn_card_mul_max_add_core_le fam hl
    rw [ht, hn] at h
    change (pointsOn fam l).card * max 1 (626349397 - (K l).card) + (K l).card ≤ 1073741824 at h
    by_contra! hsmall
    have hg : 2 ≤ 626349397 - (K l).card := by omega
    rw [max_eq_right (by omega : 1 ≤ 626349397 - (K l).card)] at h
    have hm : (pointsOn fam l).card - 1 + 1 = (pointsOn fam l).card := by omega
    have hc : 626349397 - (K l).card + (K l).card = 626349397 := by omega
    have hp := Nat.mul_le_mul_left ((pointsOn fam l).card - 1) hg
    rw [← hm, Nat.add_mul, Nat.one_mul] at h
    omega
  have hca := core a ha ra
  have hcb := core b hb rb
  have da := lineParameter_degree_lt fam ha
  have db := lineParameter_degree_lt fam hb
  have distinct : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra! he
    exact hab (Prod.ext he.1 he.2)
  have hi := FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le
    D (u 0) (u 1) (by decide : 1 ≤ 268435456) da.1 da.2 db.1 db.2 distinct
  change (K a ∩ K b).card ≤ 268435455 at hi
  let R := univ \ (K a ∪ K b)
  have hall : R.card + (K a ∪ K b).card = 1073741824 := by
    simpa only [R, card_univ, hn] using
      card_sdiff_add_card_eq_card (subset_univ (K a ∪ K b))
  have hunion := card_union_add_card_inter (K a) (K b)
  by_cases hr : R.card + 2 * 268435455 < 626349397
  · have cov := G_subset_two_lines_of_small_core_complement fam (by decide)
      (h := 626349396) ht.ge a b ha hb hr
    have hl (l : LineParameter F) (hl : l ∈ lineParameters fam) :
        (pointsOn fam l).card ≤ 447392428 :=
      TwoLargeCoreCount.line_occupancy_le fam (t := 626349397) (e := 447392427) hn ht hl
    exact ((card_le_card cov).trans (card_union_le _ _)).trans
      ((Nat.add_le_add (hl a ha) (hl b hb)).trans (by decide))
  · have hov : (K a ∩ K b).card = 268435455 := by omega
    have wd : max (a.1 - b.1).natDegree (a.2 - b.2).natDegree ≤ (K a ∩ K b).card := by
      rw [hov]
      refine max_le ((natDegree_sub_le ..).trans (max_le ?_ ?_))
        ((natDegree_sub_le ..).trans (max_le ?_ ?_)) <;> omega
    have fresh := fam.line_hproper a.1 a.2 (pointsOn fam a) da.1 da.2
      (pointsOn_subset_G fam a) (fun z hz => ((mem_pointsOn_iff fam a z).mp hz).2)
    have hc := fresh_cap D (u 0) (u 1) a.1 a.2 b.1 b.2 _ distinct wd fresh
    change (pointsOn fam a).card ≤ R.card + 1 at hc
    omega

end ArkLib.ProximityGap.Frontier.QuarterRateRichSecants
