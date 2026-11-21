/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorIncidenceAssembly
import ArkLib.Research.ProximityGap.Frontier._ThirdMomentJensenGeneral

/-! # Sharp one-line bound below the production unique-decoding endpoint

Sixty-four selected points suffice to force a large secant core by the third
moment. At distances with at least three positions of slack, each line in a
putative counterexample needs at least three fresh agreements per point.
Two lines can then cover at most the allowed number of points.
-/

set_option autoImplicit false
open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.HalfPredecessorIncidenceAssembly
open ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral
open scoped NNReal BigOperators Polynomial

namespace ArkLib.ProximityGap.Frontier.TwoLinePreUnique

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

private theorem four_point_lines_impossible (fam : BadScalarRichPointFamily dom k δ u)
    (H : Finset F) (hH : H ⊆ fam.G) (h64 : H.card = 64)
    (hn : Fintype.card ι = 1073741824) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : 536870912 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (hfour : ∀ l, (pointsOn fam l).card ≤ 4) : False := by
  classical
  let A := selectedAgreements fam
  let m (i : ι) := (H.filter fun x => i ∈ A x).card
  have hsum : ∑ i, m i = ∑ x ∈ H, (A x).card := by
    simp only [m, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hinc : 64 * 536870912 ≤ ∑ i, m i := by
    rw [hsum]
    calc
      64 * 536870912 = ∑ _x ∈ H, 536870912 := by simp [h64]
      _ ≤ ∑ x ∈ H, (A x).card := Finset.sum_le_sum fun x hx => ht.trans (fam.threshold_le x (hH hx))
  have hj := thirdMoment_jensen_lower_rat_general m 1073741824 64 536870912
    (by decide) hn (by decide) hinc
  have hu := weightedTripleSum_upper H (onFamilyLine fam) (secantParameter fam)
    (fun T => (commonCoordinates A T).card) 67108863 1073741824
    (fun a ha b hb hab => ⟨first_point_mem_pointsOn_secant fam (hH ha),
      second_point_mem_pointsOn_secant fam (hH hb) hab⟩)
    (fun l a b hab ha hb => (secantParameter_eq_of_mem_pointsOn fam l ha hb hab).symm)
    (fun l => (Finset.card_le_card (show linePoints H (onFamilyLine fam) l ⊆ pointsOn fam l
      from fun _ hx => (Finset.mem_filter.mp hx).2)).trans (hfour l))
    (fun T hT hnc => by
      have hTG := Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hT).1.trans hH, (Finset.mem_powersetCard.mp hT).2⟩
      exact (tripleWeight_le_degree_pred_of_not_collinear fam hk T hTG hnc).trans (by omega))
    (fun T _ => by
      have hc := Finset.card_le_univ (commonCoordinates A T)
      omega)
  rw [← sum_choose_incidence_eq_sum_commonCoordinates_card H A, h64] at hu
  have hu' : 6 * ∑ i, ((m i).choose 3 : ℚ) ≤
      67108863 * 64 * (64 - 1) * (64 - 2) + 2 * 1073741824 * 64 * (64 - 1) := by
    norm_num at hu ⊢
    exact_mod_cast hu
  norm_num at hj hu'
  linarith

/-- At the production length with dimension at most one sixteenth of that length,
three positions of slack force at most one more bad scalar than errors. -/
theorem production_family_card_le (fam : BadScalarRichPointFamily dom k δ u)
    {e t : ℕ} (hn : Fintype.card ι = 1073741824) (het : e + t = 1073741824)
    (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = t)
    (hsep : 2 * e + (k - 1) + 3 ≤ 1073741824) : fam.G.card ≤ e + 1 := by
  classical
  by_contra! hcounter
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  have hh : 536870912 + 1 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ := by omega
  have hpack (l : LineParameter F) (hl : l ∈ lineParameters fam) :
      (pointsOn fam l).card * max 1 (t - (D l).card) + (D l).card ≤ e + t := by
    have hp := pointsOn_card_mul_max_add_core_le fam hl
    rwa [ht, hn, ← het] at hp
  have hstrict (l : LineParameter F) (hl : l ∈ lineParameters fam) :
      3 * (pointsOn fam l).card ≤ e + 3 := by
    have hp := hpack l hl
    have hone := TwoLargeCoreCount.occupancy_le_of_packing hp
    have hpartition := pointsOn_card_add_outsideLine_card fam l
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (by omega : 0 < (outsideLine fam l).card)
    have hfresh := threshold_sub_pred_le_fresh_card fam l hk hl hg
    rw [ht] at hfresh
    have hsub : (fullAgreement dom (u 0) (u 1) g (fam.q g) \ D l) ⊆ (D l)ᶜ :=
      fun _ hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
    have hs := Finset.card_le_card hsub
    rw [Finset.card_compl, hn] at hs
    have hz := Finset.card_le_univ (D l)
    rw [hn] at hz
    have hdiff : 3 ≤ t - (D l).card := by dsimp only [D] at *; omega
    rw [max_eq_right (by omega : 1 ≤ t - (D l).card)] at hp
    cases hL : (pointsOn fam l).card with
    | zero => omega
    | succ m =>
      rw [hL, Nat.succ_mul] at hp
      have hm := Nat.mul_le_mul_left m hdiff
      omega
  have hbig : ∃ l ∈ lineParameters fam, 536870912 + 4 * (k - 1) < 2 * (D l).card + 3 := by
    by_contra! hsmall
    by_cases hsize : 64 ≤ fam.G.card
    · obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq hsize
      apply four_point_lines_impossible fam H hH hc hn hk hkmax (by omega)
      intro l
      by_cases h2 : 1 < (pointsOn fam l).card
      · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
        have hl : l ∈ lineParameters fam := by
          rw [← secantParameter_eq_of_mem_pointsOn fam l ha hb hab]
          exact secantParameter_mem_lineParameters fam (pointsOn_subset_G fam l ha)
            (pointsOn_subset_G fam l hb) hab
        have hp := hpack l hl
        have hz := hsmall l hl
        have hm := Nat.mul_le_mul_left (pointsOn fam l).card
          (show 536870912 + 1 - (D l).card ≤ max 1 (t - (D l).card) by omega)
        apply HalfPredecessorRateSixteenth.line_card_le_four (h := 536870912)
          (d := k - 1) (z := (D l).card) (by decide) (by omega) hz
        omega
      · omega
    · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < fam.G.card)
      let l := secantParameter fam a b
      have hl : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam ha hb hab
      have hal := first_point_mem_pointsOn_secant fam (beta := b) ha
      have hbl := second_point_mem_pointsOn_secant fam hb hab
      have hcore : selectedAgreements fam a ∩ selectedAgreements fam b = D l := by
        rw [selectedAgreements, selectedAgreements, (mem_pointsOn_iff fam l a).mp hal |>.2,
          (mem_pointsOn_iff fam l b).mp hbl |>.2]
        exact fullAgreement_inter_eq_jointCore dom (u 0) (u 1) l.1 l.2 hab
      have hc := Finset.card_inter_add_card_union
        (selectedAgreements fam a) (selectedAgreements fam b)
      rw [hcore] at hc
      have hu := Finset.card_le_univ (selectedAgreements fam a ∪ selectedAgreements fam b)
      rw [hn] at hu
      have ha' : t ≤ (selectedAgreements fam a).card := ht ▸ fam.threshold_le a ha
      have hb' : t ≤ (selectedAgreements fam b).card := ht ▸ fam.threshold_le b hb
      have hs := hsmall l hl
      omega
  obtain ⟨l, hl, hlarge⟩ := hbig
  have hL := hstrict l hl
  have hL2 := two_le_pointsOn_card_of_mem_lineParameters fam hl
  have hpartition := pointsOn_card_add_outsideLine_card fam l
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (outsideLine fam l).card)
  have hcover := outsideLine_subset_pointsOn_secant_of_largeCore fam hk
    (show Fintype.card ι = 2 * 536870912 by omega) hh hl ha hb hab hlarge
  have hsec := secantParameter_mem_lineParameters fam ((mem_outsideLine_iff fam l a).mp ha).1
    ((mem_outsideLine_iff fam l b).mp hb).1 hab
  have hsecond := hstrict _ hsec
  have hcount := Finset.card_le_card hcover
  omega

end ArkLib.ProximityGap.Frontier.TwoLinePreUnique

#print axioms ArkLib.ProximityGap.Frontier.TwoLinePreUnique.production_family_card_le
