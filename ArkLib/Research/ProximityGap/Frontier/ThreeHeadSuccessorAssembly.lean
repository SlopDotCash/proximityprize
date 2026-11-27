/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadSuccessorReduction
import ArkLib.Research.ProximityGap.Frontier.DimensionRaiseMCA
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass

/-! # End-to-end `ThreeHeadResidualSecant` and ten-row `ThreeHeadSuccessorIncidence` brackets (Packet L4c)

Closes Rows 2 & 3 (`k = 71,582,792` including the 9-label opposite-involution obstruction and
`k = 73,688,168`), wires `DimensionRaiseMCA.eps_mono_dimension` and `ManyHeadLocatorMass`, and
assembles the full ten-row bracket table of `docs/research/proximity-gap/three-head-successor-incidence.md`
plus `ThreeHeadResidualSecant` (`2 ≤ K ≤ 76,695,848`), conditional only on
`NonlinearComponentCap logDerivPrice`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorAssembly

open Finset Polynomial Code
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.TwoSurfaceFactorAccounting
open ArkLib.ProximityGap.Frontier.SecondPrimeEighthAssembly
open ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorReduction
open ArkLib.ProximityGap.Frontier.ThreeHeadResidualSecant
open ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorIncidence
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open scoped NNReal ENNReal

private theorem faceCost_eq_sum_charge : ∀ b : Fin 4 → Bool,
    ThreeHeadSuccessorIncidence.faceCost (EighthSaturatedOppositeDirections.count b) =
      ∑ j : Fin 4, EighthSaturatedOppositeDirections.charge b j := by
  decide

private theorem charge_eq_three_sum (b : Fin 4 → Bool) (j : Fin 4) :
    EighthSaturatedOppositeDirections.charge b j =
      (if b (EighthSaturatedOppositeDirections.face j 0) then 1 else 0) +
      (if b (EighthSaturatedOppositeDirections.face j 1) then 1 else 0) +
      (if b (EighthSaturatedOppositeDirections.face j 2) then 1 else 0) - 1 := by
  revert b j; decide

private theorem local_row2_layout : ∀ b : Fin 4 → Bool,
    2 * EighthSaturatedOppositeDirections.count b +
      (if EighthSaturatedOppositeDirections.count b = 1 ∨
          EighthSaturatedOppositeDirections.count b = 2 then 0 else 1) ≤
      2 + ThreeHeadSuccessorIncidence.faceCost (EighthSaturatedOppositeDirections.count b) := by
  decide

private theorem local_row2_split : ∀ b : Fin 4 → Bool,
    EighthSaturatedOppositeDirections.count b = 1 ∨
      EighthSaturatedOppositeDirections.count b = 2 →
    (if EighthSaturatedOppositeDirections.count b = 2 then 1 else 0) + 1 =
      EighthSaturatedOppositeDirections.count b ∧
    (if EighthSaturatedOppositeDirections.count b = 1 ∧ b 0 = false then 1 else 0) +
      (if b 0 then 1 else 0) +
      ((if b 1 then 1 else 0) + (if b 2 then 1 else 0) + (if b 3 then 1 else 0) - 1) = 1 := by
  decide

private theorem ite_one_zero_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℕ) else 0) = if q then 1 else 0 := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · have hnq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hnq]

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem lineDet_self_left' (a b : LineParameter F) : lineDeterminant a b a = 0 := by
  unfold lineDeterminant; ring

omit [Fintype F] [DecidableEq F] in
private theorem lineDet_self_right' (a b : LineParameter F) : lineDeterminant a b b = 0 := by
  unfold lineDeterminant; ring

private theorem off_core3_card {d : ℕ} (hd : 1 ≤ d + 1)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (a b c : LineParameter F)
    (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam) (hc : c ∈ lineParameters fam)
    {z : F} (hz : z ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)) :
    ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ - 3 * d ≤
      (fullAgreement dom (u 0) (u 1) z (fam.q z) \
        (jointCore dom (u 0) (u 1) a.1 a.2 ∪ jointCore dom (u 0) (u 1) b.1 b.2 ∪
          jointCore dom (u 0) (u 1) c.1 c.2)).card := by
  classical
  let A := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  have hG := (Finset.mem_sdiff.mp hz).1
  have hoff := (Finset.mem_sdiff.mp hz).2
  simp only [Finset.mem_union, not_or] at hoff
  have hi (l : LineParameter F) (hl : l ∈ lineParameters fam) (hn' : z ∉ pointsOn fam l) :
      (A ∩ D l).card ≤ d := by
    have hd' := lineParameter_degree_lt fam hl
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hd (fam.degree_lt z hG)
      hd'.1 hd'.2 (fun he => hn' ((mem_pointsOn_iff fam l z).2 ⟨hG, he⟩))
  have h1 := hi a ha hoff.1.1
  have h2 := hi b hb hoff.1.2
  have h3 := hi c hc hoff.2
  have h4 := Finset.card_union_le (A ∩ D a) (A ∩ D b)
  have h5 := Finset.card_union_le ((A ∩ D a) ∪ (A ∩ D b)) (A ∩ D c)
  have h6 := Finset.card_sdiff_add_card_inter A (D a ∪ D b ∪ D c)
  simp only [Finset.inter_union_distrib_left] at h6
  have hth := fam.threshold_le z hG
  change _ ≤ A.card at hth
  change _ ≤ (A \ (D a ∪ D b ∪ D c)).card
  omega

/-- If a fourth head `H4` carries two outside labels `g ≠ h` and is collinear with two of the
three old heads `a, b`, then `a, b` lose at least `2*τ - s` combined fresh slots. -/
private theorem collinear_fourth_impossible {d e : ℕ} (hd : 1 ≤ d + 1)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hn : Fintype.card I = N) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = N - e)
    (he : e ≤ N)
    (a b c H4 : LineParameter F)
    (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
    (hc : c ∈ lineParameters fam)
    (hab : a ≠ b) (hcoll : threeLineDeterminant a b H4 = 0)
    (hca : N - e - 1 ≤ (jointCore dom (u 0) (u 1) a.1 a.2).card)
    (hcb : N - e - 1 ≤ (jointCore dom (u 0) (u 1) b.1 b.2).card)
    (hdet : threeLineDeterminant a b c ≠ 0)
    (hcc : N - e - 1 ≤ (jointCore dom (u 0) (u 1) c.1 c.2).card)
    (hoff : (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card ≤ 2000025)
    {g h : F} (hgh : g ≠ h)
    (hg : g ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c))
    (hh : h ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c))
    (hgOn : g ∈ pointsOn fam H4) (hhOn : h ∈ pointsOn fam H4)
    (hslack : 3 * (e + 1) + 2000025 ≤
      2147483648 + (2 * (N - e - 3 * d) - (N + 2 * d - 3 * (N - e - 1)))) :
    fam.G.card ≤ 2147483648 := by
  classical
  let core3 := jointCore dom (u 0) (u 1) a.1 a.2 ∪ jointCore dom (u 0) (u 1) b.1 b.2 ∪
    jointCore dom (u 0) (u 1) c.1 c.2
  let Ag := fullAgreement dom (u 0) (u 1) g (fam.q g) \ core3
  let Ah := fullAgreement dom (u 0) (u 1) h (fam.q h) \ core3
  let W := Ag ∩ Ah
  have hWsubH4 : W ⊆ jointCore dom (u 0) (u 1) H4.1 H4.2 := by
    intro x hx
    obtain ⟨hxg, hxh⟩ := Finset.mem_inter.mp hx
    have h1 := (Finset.mem_sdiff.mp hxg).1
    have h2 := (Finset.mem_sdiff.mp hxh).1
    obtain ⟨_, hqg⟩ := (mem_pointsOn_iff fam H4 g).mp hgOn
    obtain ⟨_, hqh⟩ := (mem_pointsOn_iff fam H4 h).mp hhOn
    rw [hqg] at h1; rw [hqh] at h2
    have he1 := (Finset.mem_filter.mp h1).2
    have he2 := (Finset.mem_filter.mp h2).2
    simp only [eval_add, eval_mul, eval_C] at he1 he2
    have hv : H4.2.eval (dom x) = u 1 x := by
      have hd' : (g - h) * (H4.2.eval (dom x) - u 1 x) = 0 := by linear_combination he1 - he2
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd').resolve_left (sub_ne_zero.mpr hgh))
    have hu : H4.1.eval (dom x) = u 0 x := by rw [hv] at he1; exact add_right_cancel he1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hv⟩
  have hAg : N - e - 3 * d ≤ Ag.card := by
    have h1 := off_core3_card hd fam a b c ha hb hc hg
    rw [ht] at h1; exact h1
  have hAh : N - e - 3 * d ≤ Ah.card := by
    have h1 := off_core3_card hd fam a b c ha hb hc hh
    rw [ht] at h1; exact h1
  have hU3 : 3 * (N - e - 1) ≤ core3.card + 2 * d := by
    have hdegA := lineParameter_degree_lt fam ha
    have hdegB := lineParameter_degree_lt fam hb
    have hdegC := lineParameter_degree_lt fam hc
    have hD := natDegree_threeLineDeterminant_le_two_mul_sub_two hdegA.1 hdegA.2 hdegB.1 hdegB.2 hdegC.1 hdegC.2
    have hU := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b c hdet
    simp only [coreSet_eq_jointCore] at hU
    change (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
      (jointCore dom (u 0) (u 1) c.1 c.2).card ≤ core3.card + _ at hU
    omega
  have hWcard : 2 * (N - e - 3 * d) - (N + 2 * d - 3 * (N - e - 1)) ≤ W.card := by
    have hun := Finset.card_union_add_card_inter Ag Ah
    have hsubC : Ag ∪ Ah ⊆ Finset.univ \ core3 := by
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp h1).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp h2).2⟩
    have hle := Finset.card_le_card hsubC
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn] at hle
    change (Ag ∪ Ah).card + W.card = Ag.card + Ah.card at hun
    omega
  let availA := Finset.univ \ jointCore dom (u 0) (u 1) a.1 a.2
  let availB := Finset.univ \ jointCore dom (u 0) (u 1) b.1 b.2
  let Ga := pointsOn fam a
  let Gb := pointsOn fam b \ pointsOn fam a
  have hfresh (l : LineParameter F) (hl : l ∈ lineParameters fam) (z : F) (hz : z ∈ pointsOn fam l) :
      ∃ x : I, x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) ∧ x ∉ jointCore dom (u 0) (u 1) l.1 l.2 := by
    obtain ⟨hzG, _⟩ := (mem_pointsOn_iff fam l z).mp hz
    have hdl := lineParameter_degree_lt fam hl
    exact Finset.not_subset.mp (not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
      (fullAgreement dom (u 0) (u 1) z (fam.q z)) l.1 l.2 hdl.1 hdl.2 (fam.noJoint z hzG))
  let pickA (z : F) : I := if hz : z ∈ Ga then Classical.choose (hfresh a ha z hz) else Classical.arbitrary I
  let pickB (z : F) : I := if hz : z ∈ Gb then Classical.choose (hfresh b hb z (Finset.mem_sdiff.mp hz).1)
    else Classical.arbitrary I
  have huniq (l : LineParameter F) (z : F) (hz : z ∈ pointsOn fam l) (x : I)
      (hx : x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z))
      (ho : x ∉ jointCore dom (u 0) (u 1) l.1 l.2) :
      z = (u 0 x - l.1.eval (dom x)) / (l.2.eval (dom x) - u 1 x) := by
    obtain ⟨_, hq⟩ := (mem_pointsOn_iff fam l z).mp hz
    rw [hq] at hx
    have hag := (Finset.mem_filter.mp hx).2
    simp only [eval_add, eval_mul, eval_C] at hag
    have hden : l.2.eval (dom x) - u 1 x ≠ 0 := by
      intro h0; have hv := sub_eq_zero.mp h0
      apply ho
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv] at hag; exact add_right_cancel hag, hv⟩
    exact (eq_div_iff hden).mpr (by linear_combination hag)
  let chosenA := Ga.image pickA
  let chosenB := Gb.image pickB
  have hAcardEq : chosenA.card = Ga.card := by
    apply Finset.card_image_of_injOn
    intro z₁ hz₁ z₂ hz₂ heq
    have h1 := Classical.choose_spec (hfresh a ha z₁ hz₁)
    have h2 := Classical.choose_spec (hfresh a ha z₂ hz₂)
    have hp1 : pickA z₁ = Classical.choose (hfresh a ha z₁ hz₁) := dite_eq_left hz₁
    have hp2 : pickA z₂ = Classical.choose (hfresh a ha z₂ hz₂) := dite_eq_left hz₂
    rw [← hp1] at h1; rw [← hp2, ← heq] at h2
    exact (huniq a z₁ hz₁ _ h1.1 h1.2).trans (huniq a z₂ hz₂ _ h2.1 h2.2).symm
  have hBcardEq : chosenB.card = Gb.card := by
    apply Finset.card_image_of_injOn
    intro z₁ hz₁ z₂ hz₂ heq
    have hz₁b := (Finset.mem_sdiff.mp hz₁).1
    have hz₂b := (Finset.mem_sdiff.mp hz₂).1
    have h1 := Classical.choose_spec (hfresh b hb z₁ hz₁b)
    have h2 := Classical.choose_spec (hfresh b hb z₂ hz₂b)
    have hp1 : pickB z₁ = Classical.choose (hfresh b hb z₁ hz₁b) := dite_eq_left hz₁
    have hp2 : pickB z₂ = Classical.choose (hfresh b hb z₂ hz₂b) := dite_eq_left hz₂
    rw [← hp1] at h1; rw [← hp2, ← heq] at h2
    exact (huniq b z₁ hz₁b _ h1.1 h1.2).trans (huniq b z₂ hz₂b _ h2.1 h2.2).symm
  have hsep : ∀ x ∈ W, x ∉ chosenA ∨ x ∉ chosenB := by
    intro x hxW
    by_contra! hboth
    obtain ⟨za, hza, hpza⟩ := Finset.mem_image.mp hboth.1
    obtain ⟨zb, hzb, hpzb⟩ := Finset.mem_image.mp hboth.2
    have hzbb := (Finset.mem_sdiff.mp hzb).1
    have h1 := Classical.choose_spec (hfresh a ha za hza)
    have h2 := Classical.choose_spec (hfresh b hb zb hzbb)
    have hp1 : pickA za = Classical.choose (hfresh a ha za hza) := dite_eq_left hza
    have hp2 : pickB zb = Classical.choose (hfresh b hb zb hzbb) := dite_eq_left hzb
    rw [← hp1, hpza] at h1; rw [← hp2, hpzb] at h2
    have hxH4 : x ∈ jointCore dom (u 0) (u 1) H4.1 H4.2 := hWsubH4 hxW
    obtain ⟨_, hqa⟩ := (mem_pointsOn_iff fam a za).mp hza
    obtain ⟨_, hqb⟩ := (mem_pointsOn_iff fam b zb).mp hzbb
    rw [hqa] at h1; rw [hqb] at h2
    have hcoll' : lineDeterminant a b H4 = 0 := by
      rw [lineDet_eq_threeLineDet]; exact hcoll
    obtain ⟨huH4, hvH4⟩ := (Finset.mem_filter.mp hxH4).2
    have h1eq := (Finset.mem_filter.mp h1.1).2
    have h2eq := (Finset.mem_filter.mp h2.1).2
    simp only [eval_add, eval_mul, eval_C] at h1eq h2eq
    have hta : (a.2 - H4.2).eval (dom x) ≠ 0 := by
      rw [eval_sub, hvH4]; intro h0; have hv := sub_eq_zero.mp h0
      exact h1.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv] at h1eq; exact add_right_cancel h1eq, hv⟩)
    have hea : (a.1 - H4.1).eval (dom x) + za * (a.2 - H4.2).eval (dom x) = 0 := by
      rw [eval_sub, eval_sub, huH4, hvH4]; linear_combination h1eq
    have hzaEq := gamma_eq_primitiveScalarAt_of_pairEquation a b a H4 hab (lineDet_self_left' a b)
      hcoll' hta hea
    have htb : (b.2 - H4.2).eval (dom x) ≠ 0 := by
      rw [eval_sub, hvH4]; intro h0; have hv := sub_eq_zero.mp h0
      exact h2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv] at h2eq; exact add_right_cancel h2eq, hv⟩)
    have heb : (b.1 - H4.1).eval (dom x) + zb * (b.2 - H4.2).eval (dom x) = 0 := by
      rw [eval_sub, eval_sub, huH4, hvH4]; linear_combination h2eq
    have hzbEq := gamma_eq_primitiveScalarAt_of_pairEquation a b b H4 hab (lineDet_self_right' a b)
      hcoll' htb heb
    exact (Finset.mem_sdiff.mp hzb).2 ((hzaEq.trans hzbEq.symm) ▸ hza)
  have hmissed := EighthQuotientCoreCap.missed_pair availA availB chosenA chosenB W
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := Classical.choose_spec (hfresh a ha z hz)
      have hp : pickA z = Classical.choose (hfresh a ha z hz) := dite_eq_left hz
      rw [← hp] at h1; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1.2⟩)
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have h1 := Classical.choose_spec (hfresh b hb z (Finset.mem_sdiff.mp hz).1)
      have hp : pickB z = Classical.choose (hfresh b hb z (Finset.mem_sdiff.mp hz).1) := dite_eq_left hz
      rw [← hp] at h1; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1.2⟩)
    (fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hin =>
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).2
        (Finset.mem_union_left _ (Finset.mem_union_left _ hin))⟩)
    (fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hin =>
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).2
        (Finset.mem_union_left _ (Finset.mem_union_right _ hin))⟩)
    hsep
  have havA : availA.card ≤ e + 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]; omega
  have havB : availB.card ≤ e + 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]; omega
  have habCard : (pointsOn fam a ∪ pointsOn fam b).card = Ga.card + Gb.card := by
    have h := Finset.card_sdiff_add_card_inter (pointsOn fam b) (pointsOn fam a)
    have hu := Finset.card_union_add_card_inter (pointsOn fam a) (pointsOn fam b)
    rw [Finset.inter_comm] at h; dsimp [Ga, Gb]; omega
  have hcCard : (pointsOn fam c).card ≤ e + 1 :=
    line_occupancy_le_e_add_one fam hn (by omega) (by omega : (N - e) + e = N) hc
  have hU3sub : pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ⊆ fam.G :=
    Finset.union_subset (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
      (pointsOn_subset_G fam c)
  have hsd := Finset.card_sdiff_add_card_eq_card hU3sub
  have hu3 := Finset.card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)
  omega

/-- Construct `ThreeHeadSuccessorIncidence.Counts I m d (N - e)`. -/
private noncomputable def buildCounts {d e m : ℕ} (hd : 1 ≤ d + 1)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = N - e)
    (a b c H4 : LineParameter F)
    (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
    (hc : c ∈ lineParameters fam) (hH4 : H4 ∈ lineParameters fam)
    (hcores : ∀ x ∈ ({a, b, c} : Finset _), N - e - 1 ≤ (jointCore dom (u 0) (u 1) x.1 x.2).card)
    (htri : ∀ j : Fin 4, threeLineDeterminant
      ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 0))
      ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 1))
      ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 2)) ≠ 0)
    (Gout : Finset F) (hGoutCard : Gout.card = m)
    (hGoutOff : Gout ⊆ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c))
    (hGoutOn : Gout ⊆ pointsOn fam H4) :
    ThreeHeadSuccessorIncidence.Counts I m d (N - e) := by
  classical
  let old3 : Fin 3 → LineParameter F := ![a, b, c]
  let W : Fin 4 → LineParameter F := ![H4, a, b, c]
  let coreOf (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let oldFn (x : I) : ℕ := (Finset.univ.filter fun i : Fin 3 => x ∈ coreOf (old3 i)).card
  let fourthFn (x : I) : ℕ := if x ∈ coreOf H4 then 1 else 0
  let foldsFn (x : I) : ℕ :=
    (Gout.filter fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card
  have hWmem (i : Fin 4) : W i ∈ lineParameters fam := by
    fin_cases i <;> simp [W, ha, hb, hc, hH4]
  have hWdeg (i : Fin 4) : (W i).1.natDegree < d + 1 ∧ (W i).2.natDegree < d + 1 :=
    lineParameter_degree_lt fam (hWmem i)
  refine
    { old := oldFn
      fourth := fourthFn
      folds := foldsFn
      old_le := fun x => (Finset.card_filter_le _ _).trans (by simp)
      fourth_le := fun x => by dsimp [fourthFn]; split_ifs <;> omega
      outside := fun x hx0 => by
        have hxOut : x ∉ coreOf H4 := by dsimp [fourthFn] at hx0; split_ifs at hx0; omega
        apply Finset.card_le_one.mpr
        intro z₁ hz₁ z₂ hz₂
        obtain ⟨hz₁G, ha₁⟩ := Finset.mem_filter.mp hz₁
        obtain ⟨hz₂G, ha₂⟩ := Finset.mem_filter.mp hz₂
        obtain ⟨_, hq₁⟩ := (mem_pointsOn_iff fam H4 z₁).mp (hGoutOn hz₁G)
        obtain ⟨_, hq₂⟩ := (mem_pointsOn_iff fam H4 z₂).mp (hGoutOn hz₂G)
        rw [hq₁] at ha₁; rw [hq₂] at ha₂
        have he1 := (Finset.mem_filter.mp ha₁).2
        have he2 := (Finset.mem_filter.mp ha₂).2
        simp only [eval_add, eval_mul, eval_C] at he1 he2
        by_contra hne
        have hv : H4.2.eval (dom x) = u 1 x := by
          have hdiff : (z₁ - z₂) * (H4.2.eval (dom x) - u 1 x) = 0 := by linear_combination he1 - he2
          exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne))
        have hu : H4.1.eval (dom x) = u 0 x := by rw [hv] at he1; exact add_right_cancel he1
        exact hxOut (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hv⟩)
      onCore := fun x hx1 => by
        have hxIn : x ∈ coreOf H4 := by dsimp [fourthFn] at hx1; split_ifs at hx1; omega
        have hall : Gout.filter (fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)) = Gout := by
          apply Finset.filter_true_of_mem
          intro z hz
          obtain ⟨_, hq⟩ := (mem_pointsOn_iff fam H4 z).mp (hGoutOn hz)
          obtain ⟨hu, hv⟩ := (Finset.mem_filter.mp hxIn).2
          rw [hq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [eval_add, eval_mul, eval_C, hu, hv]⟩
        dsimp [foldsFn]; rw [hall, hGoutCard]
      rich := by
        have hsum : (∑ x : I, oldFn x) = (coreOf a).card + (coreOf b).card + (coreOf c).card := by
          simp only [oldFn, Finset.card_filter]
          rw [Finset.sum_comm, Fin.sum_univ_three]
          change (∑ x : I, if x ∈ coreOf a then 1 else 0) +
              (∑ x : I, if x ∈ coreOf b then 1 else 0) +
              (∑ x : I, if x ∈ coreOf c then 1 else 0) = _
          simp only [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        dsimp only [coreOf] at hsum
        rw [hsum]
        have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
        omega
      agreements := by
        have hsum : (∑ x : I, foldsFn x) =
            ∑ z ∈ Gout, (fullAgreement dom (u 0) (u 1) z (fam.q z)).card := by
          simp only [foldsFn, Finset.card_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro z _
          simp only [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        rw [hsum, ← hGoutCard]
        have hge : ∀ z ∈ Gout, N - e ≤ (fullAgreement dom (u 0) (u 1) z (fam.q z)).card := fun z hz => by
          have h1 := fam.threshold_le z (Finset.mem_sdiff.mp (hGoutOff hz)).1; omega
        exact (Finset.sum_le_sum hge).trans_eq' (by simp)
      oldTriangle := by
        have htri0 : threeLineDeterminant a b c ≠ 0 := by
          simpa [W, EighthSaturatedOppositeDirections.face] using htri 0
        have h1 := sum_coreCount_sub_one_le_natDegree dom (u 0) (u 1) a b c Finset.univ htri0
        have h2 := natDegree_threeLineDeterminant_le_two_mul_sub_two (hWdeg 1).1 (hWdeg 1).2
          (hWdeg 2).1 (hWdeg 2).2 (hWdeg 3).1 (hWdeg 3).2
        have heq (x : I) : oldFn x = coreCount (u 0 x) (u 1 x) (dom x) a b c := by
          simp only [oldFn, coreCount, Finset.card_filter, Fin.sum_univ_three]
          change (if x ∈ coreOf a then 1 else 0) + (if x ∈ coreOf b then 1 else 0) +
              (if x ∈ coreOf c then 1 else 0) = _
          have hmem (l : LineParameter F) : x ∈ coreOf l ↔ AgreesAt (u 0 x) (u 1 x) (dom x) l := by
            simp [coreOf, jointCore, AgreesAt]
          exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (ite_one_zero_iff (hmem a)) (ite_one_zero_iff (hmem b)))
            (ite_one_zero_iff (hmem c))
        simp_rw [heq]
        exact (h1.trans h2).trans (by omega)
      foldRoots := by
        have hroots : ∀ z ∈ Gout, ∀ i : Fin 3,
            (coreOf (old3 i) ∩ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ d := by
          intro z hz i
          have hzOff := hGoutOff hz
          have hzG := (Finset.mem_sdiff.mp hzOff).1
          have hzNot := (Finset.mem_sdiff.mp hzOff).2
          simp only [Finset.mem_union, not_or] at hzNot
          rw [Finset.inter_comm]
          have hdi : (old3 i).1.natDegree < d + 1 ∧ (old3 i).2.natDegree < d + 1 := by
            fin_cases i <;> [exact hWdeg 1; exact hWdeg 2; exact hWdeg 3]
          have hneq : fam.q z ≠ (old3 i).1 + C z * (old3 i).2 := by
            intro heq
            fin_cases i
            · exact hzNot.1.1 ((mem_pointsOn_iff fam a z).mpr ⟨hzG, heq⟩)
            · exact hzNot.1.2 ((mem_pointsOn_iff fam b z).mpr ⟨hzG, heq⟩)
            · exact hzNot.2 ((mem_pointsOn_iff fam c z).mpr ⟨hzG, heq⟩)
          have hle := fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hd (fam.degree_lt z hzG)
            hdi.1 hdi.2 hneq
          dsimp only [coreOf]; omega
        have hfi := ThreeHeadSuccessorIncidence.fold_intersections Gout (fun i => coreOf (old3 i))
          (fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)) d hroots
        rwa [hGoutCard] at hfi
      faces := by
        let bm (x : I) (i : Fin 4) : Bool := decide (AgreesAt (u 0 x) (u 1 x) (dom x) (W i))
        have hbm (x : I) (i : Fin 4) : bm x i = true ↔ x ∈ coreOf (W i) := by
          simp only [bm, decide_eq_true_eq]; simp [coreOf, jointCore, AgreesAt]
        have hcnt (x : I) : oldFn x + fourthFn x = EighthSaturatedOppositeDirections.count (bm x) := by
          rw [count_eq_four_sum]
          simp only [oldFn, fourthFn, Finset.card_filter, Fin.sum_univ_three]
          change (if x ∈ coreOf a then 1 else 0) + (if x ∈ coreOf b then 1 else 0) +
              (if x ∈ coreOf c then 1 else 0) + (if x ∈ coreOf H4 then 1 else 0) = _
          have h0 : (if bm x 0 = true then 1 else 0) = if x ∈ coreOf H4 then 1 else 0 :=
            ite_one_zero_iff (hbm x 0)
          have h1 : (if bm x 1 = true then 1 else 0) = if x ∈ coreOf a then 1 else 0 :=
            ite_one_zero_iff (hbm x 1)
          have h2 : (if bm x 2 = true then 1 else 0) = if x ∈ coreOf b then 1 else 0 :=
            ite_one_zero_iff (hbm x 2)
          have h3 : (if bm x 3 = true then 1 else 0) = if x ∈ coreOf c then 1 else 0 :=
            ite_one_zero_iff (hbm x 3)
          omega
        simp_rw [hcnt, faceCost_eq_sum_charge]
        rw [Finset.sum_comm]
        have hface (j : Fin 4) : (∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) j) ≤ 2 * d := by
          have h1 := sum_coreCount_sub_one_le_natDegree dom (u 0) (u 1)
            (W (EighthSaturatedOppositeDirections.face j 0))
            (W (EighthSaturatedOppositeDirections.face j 1))
            (W (EighthSaturatedOppositeDirections.face j 2)) Finset.univ (htri j)
          have h2 := natDegree_threeLineDeterminant_le_two_mul_sub_two
            (hWdeg (EighthSaturatedOppositeDirections.face j 0)).1
            (hWdeg (EighthSaturatedOppositeDirections.face j 0)).2
            (hWdeg (EighthSaturatedOppositeDirections.face j 1)).1
            (hWdeg (EighthSaturatedOppositeDirections.face j 1)).2
            (hWdeg (EighthSaturatedOppositeDirections.face j 2)).1
            (hWdeg (EighthSaturatedOppositeDirections.face j 2)).2
          have heq : (∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) j) =
              ∑ x : I, (coreCount (u 0 x) (u 1 x) (dom x)
                (W (EighthSaturatedOppositeDirections.face j 0))
                (W (EighthSaturatedOppositeDirections.face j 1))
                (W (EighthSaturatedOppositeDirections.face j 2)) - 1) := by
            apply Finset.sum_congr rfl; intro x _
            rw [charge_eq_three_sum]; simp [bm, coreCount]
          rw [heq]
          exact (h1.trans h2).trans (by omega)
        exact (Finset.sum_le_sum fun j _ => hface j).trans_eq (by simp; omega) }

private theorem fourth_head_all_triangles_nonzero {d e : ℕ} (hd : 1 ≤ d + 1) (he : e ≤ N)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hn : Fintype.card I = N) (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = N - e)
    (a b c : LineParameter F)
    (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam) (hc : c ∈ lineParameters fam)
    (hdet : threeLineDeterminant a b c ≠ 0)
    (hcores : ∀ x ∈ ({a, b, c} : Finset _), N - e - 1 ≤ (jointCore dom (u 0) (u 1) x.1 x.2).card)
    (hoff : (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card ≤ 2000025)
    (hsecGap : 2 * (N + 2 * d - 3 * (N - e - 1)) + d < 3 * (N - e - 3 * d))
    (hslack : 3 * (e + 1) + 2000025 ≤
      2147483648 + (2 * (N - e - 3 * d) - (N + 2 * d - 3 * (N - e - 1))))
    (hover : 2147483648 < fam.G.card)
    (h2out : 2 ≤ (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card) :
    ∃ H4 ∈ lineParameters fam,
      fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c) ⊆ pointsOn fam H4 ∧
      ∀ j : Fin 4, threeLineDeterminant
        ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 0))
        ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 1))
        ((![H4, a, b, c] : Fin 4 → LineParameter F) (EighthSaturatedOppositeDirections.face j 2)) ≠ 0 := by
  classical
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card)
  let H4 := secantParameter fam g h
  have hH4 : H4 ∈ lineParameters fam :=
    secantParameter_mem_lineParameters fam (Finset.mem_sdiff.mp hg).1 (Finset.mem_sdiff.mp hh).1 hgh
  have hU : 3 * (N - e - 1) ≤ (jointCore dom (u 0) (u 1) a.1 a.2 ∪
      jointCore dom (u 0) (u 1) b.1 b.2 ∪ jointCore dom (u 0) (u 1) c.1 c.2).card + 2 * d := by
    have hdegA := lineParameter_degree_lt fam ha
    have hdegB := lineParameter_degree_lt fam hb
    have hdegC := lineParameter_degree_lt fam hc
    have hD := natDegree_threeLineDeterminant_le_two_mul_sub_two hdegA.1 hdegA.2 hdegB.1 hdegB.2 hdegC.1 hdegC.2
    have hU' := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b c hdet
    simp only [coreSet_eq_jointCore] at hU'
    have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
    omega
  have hsub : fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c) ⊆ pointsOn fam H4 :=
    ThreeHeadResidualSecant.outside_secant fam hd a b c (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
      (by
        change 2 * (Fintype.card I - (jointCore dom (u 0) (u 1) a.1 a.2 ∪
          jointCore dom (u 0) (u 1) b.1 b.2 ∪ jointCore dom (u 0) (u 1) c.1 c.2).card) + (d + 1 - 1) <
          3 * (⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ - 3 * (d + 1 - 1))
        rw [ht, hn]; simp only [Nat.add_sub_cancel]; omega) hgh hg hh
  have hgOn : g ∈ pointsOn fam H4 := hsub hg
  have hhOn : h ∈ pointsOn fam H4 := hsub hh
  refine ⟨H4, hH4, hsub, ?_⟩
  have hab : a ≠ b := by intro he; subst he; apply hdet; unfold threeLineDeterminant; ring
  have hac : a ≠ c := by intro he; subst he; apply hdet; unfold threeLineDeterminant; ring
  have hbc : b ≠ c := by intro he; subst he; apply hdet; unfold threeLineDeterminant; ring
  have hdetAC : threeLineDeterminant a c b ≠ 0 := by
    intro hz; apply hdet; unfold threeLineDeterminant at hz ⊢; linear_combination -hz
  have hdetBC : threeLineDeterminant b c a ≠ 0 := by
    intro hz; apply hdet; unfold threeLineDeterminant at hz ⊢; linear_combination hz
  have hdetFlip (x y z : LineParameter F) :
      threeLineDeterminant x y z = 0 → threeLineDeterminant y z x = 0 := by
    intro hz; unfold threeLineDeterminant at hz ⊢; linear_combination hz
  have hUeqBC : pointsOn fam b ∪ pointsOn fam c ∪ pointsOn fam a =
      pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c := by
    rw [Finset.union_comm _ (pointsOn fam a), Finset.union_assoc]
  have hUeqAC : pointsOn fam a ∪ pointsOn fam c ∪ pointsOn fam b =
      pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c := by
    rw [Finset.union_right_comm]
  intro j
  fin_cases j
  · simpa [EighthSaturatedOppositeDirections.face] using hdet
  · intro hz
    have hcol := hdetFlip H4 b c (by simpa [EighthSaturatedOppositeDirections.face] using hz)
    have hle := collinear_fourth_impossible hd fam hn ht he b c a H4 hb hc ha hbc hcol
      (hcores b (by simp)) (hcores c (by simp)) hdetBC (hcores a (by simp))
      (by rwa [hUeqBC]) hgh (by rwa [hUeqBC]) (by rwa [hUeqBC]) hgOn hhOn hslack
    omega
  · intro hz
    have hcol := hdetFlip H4 a c (by simpa [EighthSaturatedOppositeDirections.face] using hz)
    have hle := collinear_fourth_impossible hd fam hn ht he a c b H4 ha hc hb hac hcol
      (hcores a (by simp)) (hcores c (by simp)) hdetAC (hcores b (by simp))
      (by rwa [hUeqAC]) hgh (by rwa [hUeqAC]) (by rwa [hUeqAC]) hgOn hhOn hslack
    omega
  · intro hz
    have hcol := hdetFlip H4 a b (by simpa [EighthSaturatedOppositeDirections.face] using hz)
    have hle := collinear_fourth_impossible hd fam hn ht he a b c H4 ha hb hc hab hcol
      (hcores a (by simp)) (hcores b (by simp)) hdet (hcores c (by simp)) hoff
      hgh hg hh hgOn hhOn hslack
    omega

/-- Row 3 (`k = 73,688,168`, `e = 715,827,878`): twelve outside witnesses contradict
`ThreeHeadSuccessorIncidence.impossible_cells.2`. -/
theorem successor_row3_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 73688168 δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913946)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  by_contra! hover
  obtain ⟨a, b, c, ha, hb, hc, hdet, hcores, hoff⟩ :=
    three_saturated_noncollinear_of_over_budget hcap (d := 73688167) (e := 715827878)
      (by decide) (by decide) (by decide) fam hn ht hchar hover
  have hbd (x : LineParameter F) (hx : x ∈ lineParameters fam) : (pointsOn fam x).card ≤ 715827879 :=
    line_occupancy_le_e_add_one fam hn (by omega) (by decide : 357913946 + 715827878 = N) hx
  have hU3sub : pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ⊆ fam.G :=
    Finset.union_subset (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
      (pointsOn_subset_G fam c)
  have hsd := Finset.card_sdiff_add_card_eq_card hU3sub
  have hu3 := (Finset.card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have h12 : 12 ≤ (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card := by
    have := hbd a ha; have := hbd b hb; have := hbd c hc; omega
  obtain ⟨H4, hH4, hsubH4, htri⟩ := fourth_head_all_triangles_nonzero (d := 73688167) (e := 715827878)
    (by decide) (by decide) fam hn ht a b c ha hb hc hdet hcores hoff
    (by decide) (by decide) hover (by omega)
  obtain ⟨Gout, hGsub, hGcard⟩ := Finset.exists_subset_card_eq h12
  let C := buildCounts (d := 73688167) (e := 715827878) (m := 12) (by decide) fam ht
    a b c H4 ha hb hc hH4 hcores htri Gout hGcard hGsub (hGsub.trans hsubH4)
  exact (ThreeHeadSuccessorIncidence.impossible_cells hn).2.false C

set_option maxHeartbeats 800000 in
/-- Row 2 (`k = 71,582,792`, `e = 715,827,879`): ten outside witnesses contradict
`impossible_cells.1`; nine outside witnesses force full saturation (`nine_saturation`) and
contradict `nine_double_slots` via `FourHeadCoreDeterminant.saturated_direction_form`. -/
theorem successor_row2_badCount_le (hcap : NonlinearComponentCap logDerivPrice)
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom 71582792 δ u)
    (hn : Fintype.card I = N)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 357913945)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F) :
    fam.G.card ≤ 2147483648 := by
  classical
  by_contra! hover
  obtain ⟨a, b, c, ha, hb, hc, hdet, hcores, hoff⟩ :=
    three_saturated_noncollinear_of_over_budget hcap (d := 71582791) (e := 715827879)
      (by decide) (by decide) (by decide) fam hn ht hchar hover
  have hbd (x : LineParameter F) (hx : x ∈ lineParameters fam) : (pointsOn fam x).card ≤ 715827880 :=
    line_occupancy_le_e_add_one fam hn (by omega) (by decide : 357913945 + 715827879 = N) hx
  let U3 := pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c
  have hU3sub : U3 ⊆ fam.G :=
    Finset.union_subset (Finset.union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
      (pointsOn_subset_G fam c)
  have hsd := Finset.card_sdiff_add_card_eq_card hU3sub
  have hu3 := (Finset.card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hpa := hbd a ha; have hpb := hbd b hb; have hpc := hbd c hc
  have h9 : 9 ≤ (fam.G \ U3).card := by dsimp only [U3] at hsd ⊢; omega
  obtain ⟨H4, hH4, hsubH4, htri⟩ := fourth_head_all_triangles_nonzero (d := 71582791) (e := 715827879)
    (by decide) (by decide) fam hn ht a b c ha hb hc hdet hcores hoff
    (by decide) (by decide) hover (by dsimp only [U3] at h9; omega)
  by_cases h10 : 10 ≤ (fam.G \ U3).card
  · obtain ⟨Gout, hGsub, hGcard⟩ := Finset.exists_subset_card_eq h10
    let C := buildCounts (d := 71582791) (e := 715827879) (m := 10) (by decide) fam ht
      a b c H4 ha hb hc hH4 hcores htri Gout hGcard hGsub (hGsub.trans hsubH4)
    exact (ThreeHeadSuccessorIncidence.impossible_cells hn).1.false C
  · have hGoutCard : (fam.G \ U3).card = 9 := by omega
    let Gout := fam.G \ U3
    let C := buildCounts (d := 71582791) (e := 715827879) (m := 9) (by decide) fam ht
      a b c H4 ha hb hc hH4 hcores htri Gout hGoutCard Subset.rfl hsubH4
    let W : Fin 4 → LineParameter F := ![H4, a, b, c]
    have hWmem (i : Fin 4) : W i ∈ lineParameters fam := by
      fin_cases i <;> simp [W, ha, hb, hc, hH4]
    have hWdeg (i : Fin 4) : (W i).1.natDegree < 71582792 ∧ (W i).2.natDegree < 71582792 :=
      lineParameter_degree_lt fam (hWmem i)
    have hH4ne : H4 ≠ a ∧ H4 ≠ b ∧ H4 ≠ c := by
      obtain ⟨g, hg⟩ := Finset.card_pos.mp (by dsimp only [Gout]; omega : 0 < Gout.card)
      have hgOff := (Finset.mem_sdiff.mp hg).2
      have hgOn : g ∈ pointsOn fam H4 := hsubH4 hg
      simp only [U3, Finset.mem_union, not_or] at hgOff
      exact ⟨fun he => hgOff.1.1 (he ▸ hgOn), fun he => hgOff.1.2 (he ▸ hgOn), fun he => hgOff.2 (he ▸ hgOn)⟩
    have h4c := ThreeHeadResidualSecant.fourth_core fam a b c H4 (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) hdet hH4ne.1 hH4ne.2.1 hH4ne.2.2
    rw [hn] at h4c
    change (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
      (jointCore dom (u 0) (u 1) c.1 c.2).card + (jointCore dom (u 0) (u 1) H4.1 H4.2).card ≤
      N + 4 * 71582791 at h4c
    have hOldSum : (∑ x : I, C.old x) = (jointCore dom (u 0) (u 1) a.1 a.2).card +
        (jointCore dom (u 0) (u 1) b.1 b.2).card + (jointCore dom (u 0) (u 1) c.1 c.2).card := by
      simp only [C, buildCounts, Finset.card_filter]
      rw [Finset.sum_comm, Fin.sum_univ_three]
      change (∑ x : I, if x ∈ jointCore dom (u 0) (u 1) a.1 a.2 then 1 else 0) +
          (∑ x : I, if x ∈ jointCore dom (u 0) (u 1) b.1 b.2 then 1 else 0) +
          (∑ x : I, if x ∈ jointCore dom (u 0) (u 1) c.1 c.2 then 1 else 0) = _
      simp only [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hFourthSum : (∑ x : I, C.fourth x) = (jointCore dom (u 0) (u 1) H4.1 H4.2).card := by
      simp only [C, buildCounts, ← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hSumC : (∑ x : I, (C.old x + C.fourth x)) =
        (jointCore dom (u 0) (u 1) a.1 a.2).card + (jointCore dom (u 0) (u 1) b.1 b.2).card +
        (jointCore dom (u 0) (u 1) c.1 c.2).card + (jointCore dom (u 0) (u 1) H4.1 H4.2).card := by
      rw [Finset.sum_add_distrib, hOldSum, hFourthSum]
    obtain ⟨hSat4, hSat3⟩ := ThreeHeadSuccessorIncidence.nine_saturation hn C
      (by dsimp only [N] at h4c; omega)
    have hca := hcores a (by simp); have hcb := hcores b (by simp); have hcc := hcores c (by simp)
    dsimp only [N] at hca hcb hcc
    have hcaEq : (jointCore dom (u 0) (u 1) a.1 a.2).card = 357913944 := by omega
    have hcbEq : (jointCore dom (u 0) (u 1) b.1 b.2).card = 357913944 := by omega
    have hccEq : (jointCore dom (u 0) (u 1) c.1 c.2).card = 357913944 := by omega
    have hc4Eq : (jointCore dom (u 0) (u 1) H4.1 H4.2).card = 286331156 := by omega
    let bm (x : I) (i : Fin 4) : Bool := decide (AgreesAt (u 0 x) (u 1 x) (dom x) (W i))
    have hbm (x : I) (i : Fin 4) : bm x i = true ↔ AgreesAt (u 0 x) (u 1 x) (dom x) (W i) := by
      simp only [bm, decide_eq_true_eq]
    have hbmMem (x : I) (i : Fin 4) : bm x i = true ↔ x ∈ jointCore dom (u 0) (u 1) (W i).1 (W i).2 := by
      rw [hbm]; simp [jointCore, AgreesAt]
    have hcnt (x : I) : C.old x + C.fourth x = EighthSaturatedOppositeDirections.count (bm x) := by
      rw [count_eq_four_sum]
      simp only [C, buildCounts, Finset.card_filter, Fin.sum_univ_three]
      change (if x ∈ jointCore dom (u 0) (u 1) a.1 a.2 then 1 else 0) +
          (if x ∈ jointCore dom (u 0) (u 1) b.1 b.2 then 1 else 0) +
          (if x ∈ jointCore dom (u 0) (u 1) c.1 c.2 then 1 else 0) +
          (if x ∈ jointCore dom (u 0) (u 1) H4.1 H4.2 then 1 else 0) = _
      have h0 : (if bm x 0 = true then 1 else 0) = if x ∈ jointCore dom (u 0) (u 1) H4.1 H4.2 then 1 else 0 :=
        ite_one_zero_iff (hbmMem x 0)
      have h1 : (if bm x 1 = true then 1 else 0) = if x ∈ jointCore dom (u 0) (u 1) a.1 a.2 then 1 else 0 :=
        ite_one_zero_iff (hbmMem x 1)
      have h2 : (if bm x 2 = true then 1 else 0) = if x ∈ jointCore dom (u 0) (u 1) b.1 b.2 then 1 else 0 :=
        ite_one_zero_iff (hbmMem x 2)
      have h3 : (if bm x 3 = true then 1 else 0) = if x ∈ jointCore dom (u 0) (u 1) c.1 c.2 then 1 else 0 :=
        ite_one_zero_iff (hbmMem x 3)
      omega
    let exFn (x : I) := if EighthSaturatedOppositeDirections.count (bm x) = 1 ∨
        EighthSaturatedOppositeDirections.count (bm x) = 2 then 0 else 1
    have hlay := Finset.sum_le_sum (s := (Finset.univ : Finset I)) fun x _ => local_row2_layout (bm x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hlay
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hn] at hlay
    have hfcEq : (∑ x : I, ThreeHeadSuccessorIncidence.faceCost (EighthSaturatedOppositeDirections.count (bm x))) =
        ∑ x : I, ThreeHeadSuccessorIncidence.faceCost (C.old x + C.fourth x) := by
      apply Finset.sum_congr rfl; intro x _; rw [hcnt x]
    have hcntEq : (∑ x : I, EighthSaturatedOppositeDirections.count (bm x)) = 1360072988 := by
      rw [← hSat4]; apply Finset.sum_congr rfl; intro x _; exact (hcnt x).symm
    have hfacesLe := C.faces
    dsimp only [N] at hlay
    have hex0 : (∑ x : I, exFn x) = 0 := by dsimp [exFn] at hlay ⊢; omega
    have hreg (x : I) : EighthSaturatedOppositeDirections.count (bm x) = 1 ∨
        EighthSaturatedOppositeDirections.count (bm x) = 2 := by
      by_contra hneg
      have h1 : exFn x = 1 := by simp [exFn, hneg]
      have hle := Finset.single_le_sum (f := exFn) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
      omega
    have hfacesEq : (∑ x : I, ThreeHeadSuccessorIncidence.faceCost (C.old x + C.fourth x)) = 8 * 71582791 := by
      omega
    have hOldTriEq : (∑ x : I, ((if bm x 1 then 1 else 0) + (if bm x 2 then 1 else 0) +
        (if bm x 3 then 1 else 0) - 1)) = 2 * 71582791 := by
      have hfaceSum : (∑ x : I, ThreeHeadSuccessorIncidence.faceCost (C.old x + C.fourth x)) =
          ∑ j : Fin 4, ∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) j := by
        rw [← hfcEq, Finset.sum_comm]; simp_rw [faceCost_eq_sum_charge]
      have hfaceLe (j : Fin 4) : (∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) j) ≤ 2 * 71582791 := by
        have h1 := sum_coreCount_sub_one_le_natDegree dom (u 0) (u 1)
          (W (EighthSaturatedOppositeDirections.face j 0))
          (W (EighthSaturatedOppositeDirections.face j 1))
          (W (EighthSaturatedOppositeDirections.face j 2)) Finset.univ (htri j)
        have h2 := natDegree_threeLineDeterminant_le_two_mul_sub_two
          (hWdeg (EighthSaturatedOppositeDirections.face j 0)).1
          (hWdeg (EighthSaturatedOppositeDirections.face j 0)).2
          (hWdeg (EighthSaturatedOppositeDirections.face j 1)).1
          (hWdeg (EighthSaturatedOppositeDirections.face j 1)).2
          (hWdeg (EighthSaturatedOppositeDirections.face j 2)).1
          (hWdeg (EighthSaturatedOppositeDirections.face j 2)).2
        have heq : (∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) j) =
            ∑ x : I, (coreCount (u 0 x) (u 1 x) (dom x)
              (W (EighthSaturatedOppositeDirections.face j 0))
              (W (EighthSaturatedOppositeDirections.face j 1))
              (W (EighthSaturatedOppositeDirections.face j 2)) - 1) := by
          apply Finset.sum_congr rfl; intro x _
          rw [charge_eq_three_sum]; simp [bm, coreCount]
        rw [heq]; exact (h1.trans h2).trans (by omega)
      have h0eq : (∑ x : I, EighthSaturatedOppositeDirections.charge (bm x) 0) = 2 * 71582791 := by
        rw [Fin.sum_univ_four] at hfaceSum
        have h0 := hfaceLe 0; have h1 := hfaceLe 1; have h2 := hfaceLe 2; have h3 := hfaceLe 3
        omega
      rw [← h0eq]
      apply Finset.sum_congr rfl; intro x _
      rw [charge_eq_three_sum]; simp [EighthSaturatedOppositeDirections.face]
    have hsplit1 := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl
      fun x _ => (local_row2_split (bm x) (hreg x)).1
    have hsplit2 := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl
      fun x _ => (local_row2_split (bm x) (hreg x)).2
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      hn, Finset.sum_boole, Nat.cast_id] at hsplit1 hsplit2
    have hDoubCard : (Finset.univ.filter fun x : I => EighthSaturatedOppositeDirections.count (bm x) = 2).card =
        4 * 71582791 := by dsimp only [N] at hsplit1; omega
    have hfourthSum : (Finset.univ.filter fun x : I => bm x 0 = true).card = 286331156 := by
      have : (Finset.univ.filter fun x : I => bm x 0 = true) = jointCore dom (u 0) (u 1) H4.1 H4.2 := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbmMem, W, Matrix.cons_val_zero]
      rw [this, hc4Eq]
    let P := Finset.univ.filter fun x : I =>
      EighthSaturatedOppositeDirections.count (bm x) = 1 ∧ bm x 0 = false
    have hPcard : P.card = 644245086 := by
      change P.card + (Finset.univ.filter fun x : I => bm x 0 = true).card +
        (∑ x : I, ((if bm x 1 then 1 else 0) + (if bm x 2 then 1 else 0) +
          (if bm x 3 then 1 else 0) - 1)) = N at hsplit2
      dsimp [N] at hsplit2
      omega
    let E := (Finset.univ.filter fun x : I => EighthSaturatedOppositeDirections.count (bm x) = 2).image dom
    have hE : E.card = 4 * 71582791 := by rw [Finset.card_image_of_injective _ dom.injective, hDoubCard]
    have htr : FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 1 2 *
        FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 1 3 *
        FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 0 2 3 *
        FourHeadCoreDeterminant.triangle (fun i => (W i).1) (fun i => (W i).2) 1 2 3 ≠ 0 := by
      have htriEq (i j k : Fin 4) :
          FourHeadCoreDeterminant.triangle (fun r => (W r).1) (fun r => (W r).2) i j k =
            threeLineDeterminant (W i) (W j) (W k) := by
        unfold FourHeadCoreDeterminant.triangle threeLineDeterminant; ring
      rw [htriEq 0 1 2, htriEq 0 1 3, htriEq 0 2 3, htriEq 1 2 3]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (htri 3) (htri 2)) (htri 1)) (htri 0)
    obtain ⟨fa, fb, fc, hdisc, hform⟩ := FourHeadCoreDeterminant.saturated_direction_form
      (fun i => (W i).1) (fun i => (W i).2) 71582791
      (fun i => Nat.le_of_lt_succ (hWdeg i).1) (fun i => Nat.le_of_lt_succ (hWdeg i).2)
      htr E hE (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        let O := Finset.univ.filter fun i : Fin 4 => bm x i = true
        have hO : O.card = 2 := by
          rw [card_true_eq_count (bm x)]; exact (Finset.mem_filter.mp hx).2
        exact ⟨O, u 0 x, u 1 x, hO, fun i hi => (hbm x i).mp (Finset.mem_filter.mp hi).2⟩)
    have hOldFull (k : Fin 3) : (pointsOn fam (W k.succ)).card = 715827880 := by
      dsimp only [U3] at hsd hGoutCard
      fin_cases k <;> simp [W] <;> omega
    have hOldDisj : Pairwise (fun i j : Fin 3 => Disjoint (pointsOn fam (W i.succ)) (pointsOn fam (W j.succ))) := by
      have hsumU3 : (pointsOn fam a).card + (pointsOn fam b).card + (pointsOn fam c).card = U3.card := by
        dsimp only [U3] at hsd hGoutCard ⊢; omega
      have habDis : Disjoint (pointsOn fam a) (pointsOn fam b) := by
        have h1 := Finset.card_union_add_card_inter (pointsOn fam a) (pointsOn fam b)
        have h2 := Finset.card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)
        dsimp only [U3] at hsumU3; exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
      have hacDis : Disjoint (pointsOn fam a) (pointsOn fam c) := by
        have h1 := Finset.card_union_add_card_inter (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)
        have h2 := Finset.card_union_le (pointsOn fam a) (pointsOn fam b)
        have h3 := Finset.card_le_card (Finset.inter_subset_inter
          (Finset.subset_union_left (s₁ := pointsOn fam a) (s₂ := pointsOn fam b))
          (Subset.rfl : pointsOn fam c ⊆ pointsOn fam c))
        dsimp only [U3] at hsumU3; exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
      have hbcDis : Disjoint (pointsOn fam b) (pointsOn fam c) := by
        have h1 := Finset.card_union_add_card_inter (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)
        have h2 := Finset.card_union_le (pointsOn fam a) (pointsOn fam b)
        have h3 := Finset.card_le_card (Finset.inter_subset_inter
          (Finset.subset_union_right (s₁ := pointsOn fam a) (s₂ := pointsOn fam b))
          (Subset.rfl : pointsOn fam c ⊆ pointsOn fam c))
        dsimp only [U3] at hsumU3; exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [W] at hij ⊢
      · exact habDis
      · exact hacDis
      · exact habDis.symm
      · exact hbcDis
      · exact hacDis.symm
      · exact hbcDis.symm
    have hfreshEq {i : Fin 4} {z : F} {x : I}
        (hz : z ∈ pointsOn fam (W i))
        (hx : x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z))
        (hxout : x ∉ jointCore dom (u 0) (u 1) (W i).1 (W i).2) :
        ((W i).2.eval (dom x) - u 1 x) ≠ 0 ∧
        ((W i).1.eval (dom x) - u 0 x) + z * ((W i).2.eval (dom x) - u 1 x) = 0 ∧
        z = (u 0 x - (W i).1.eval (dom x)) / ((W i).2.eval (dom x) - u 1 x) := by
      obtain ⟨_, hq⟩ := (mem_pointsOn_iff fam (W i) z).mp hz
      rw [hq] at hx
      have hag := (Finset.mem_filter.mp hx).2
      simp only [eval_add, eval_mul, eval_C] at hag
      have hden : (W i).2.eval (dom x) - u 1 x ≠ 0 := by
        intro h0; have hv := sub_eq_zero.mp h0
        apply hxout
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv] at hag; exact add_right_cancel hag, hv⟩
      exact ⟨hden, by linear_combination hag, (eq_div_iff hden).mpr (by linear_combination hag)⟩
    have hOldSurj (k : Fin 3) (x : I) (hx : x ∉ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2) :
        ∃ z ∈ pointsOn fam (W k.succ), x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) := by
      have hhas (z : F) (hz : z ∈ pointsOn fam (W k.succ)) :
          ∃ y : I, y ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) ∧
            y ∉ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2 := by
        obtain ⟨hzG, _⟩ := (mem_pointsOn_iff fam (W k.succ) z).mp hz
        exact Finset.not_subset.mp (not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
          (fullAgreement dom (u 0) (u 1) z (fam.q z)) (W k.succ).1 (W k.succ).2
          (hWdeg k.succ).1 (hWdeg k.succ).2 (fam.noJoint z hzG))
      let f (z : F) : I := if hz : z ∈ pointsOn fam (W k.succ) then Classical.choose (hhas z hz)
        else Classical.arbitrary I
      have hinj : Set.InjOn f ↑(pointsOn fam (W k.succ)) := by
        intro z₁ hz₁ z₂ hz₂ heq
        have h1 := Classical.choose_spec (hhas z₁ hz₁)
        have h2 := Classical.choose_spec (hhas z₂ hz₂)
        have hf1 : f z₁ = Classical.choose (hhas z₁ hz₁) := dite_eq_left hz₁
        have hf2 : f z₂ = Classical.choose (hhas z₂ hz₂) := dite_eq_left hz₂
        rw [← hf1] at h1; rw [← hf2, ← heq] at h2
        exact (hfreshEq hz₁ h1.1 h1.2).2.2.trans (hfreshEq hz₂ h2.1 h2.2).2.2.symm
      have hsubOut : (pointsOn fam (W k.succ)).image f ⊆
          Finset.univ \ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2 := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        have h1 := Classical.choose_spec (hhas z hz)
        have hf1 : f z = Classical.choose (hhas z hz) := dite_eq_left hz
        rw [← hf1] at h1; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1.2⟩
      have houtCard : (Finset.univ \ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2).card = 715827880 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]
        fin_cases k <;> simp [W, hcaEq, hcbEq, hccEq, N]
      have heqImg : (pointsOn fam (W k.succ)).image f =
          Finset.univ \ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2 :=
        Finset.eq_of_subset_of_card_le hsubOut
          (by rw [Finset.card_image_of_injOn hinj, hOldFull k, houtCard])
      have hxImg : x ∈ (pointsOn fam (W k.succ)).image f := by
        rw [heqImg]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      obtain ⟨z, hz, hfz⟩ := Finset.mem_image.mp hxImg
      have h1 := Classical.choose_spec (hhas z hz)
      have hf1 : f z = Classical.choose (hhas z hz) := dite_eq_left hz
      rw [← hf1, hfz] at h1; exact ⟨z, hz, h1.1⟩
    let freshH4 (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z) \ jointCore dom (u 0) (u 1) H4.1 H4.2
    let T := Gout.biUnion freshH4
    have hTge : 9 * 71582789 ≤ T.card := by
      have hdis : ∀ z₁ ∈ Gout, ∀ z₂ ∈ Gout, z₁ ≠ z₂ → Disjoint (freshH4 z₁) (freshH4 z₂) := by
        intro z₁ hz₁ z₂ hz₂ hne
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        obtain ⟨ha₁, ho₁⟩ := Finset.mem_sdiff.mp hx₁
        obtain ⟨ha₂, _⟩ := Finset.mem_sdiff.mp hx₂
        exact hne ((hfreshEq (i := 0) (hsubH4 hz₁) ha₁ ho₁).2.2.trans
          (hfreshEq (i := 0) (hsubH4 hz₂) ha₂ ho₁).2.2.symm)
      rw [Finset.card_biUnion (fun z₁ hz₁ z₂ hz₂ hne => hdis z₁ hz₁ z₂ hz₂ hne)]
      have hge (z : F) (hz : z ∈ Gout) : 71582789 ≤ (freshH4 z).card := by
        have hth := fam.threshold_le z (Finset.mem_sdiff.mp hz).1
        rw [ht] at hth
        have hsd' := Finset.card_sdiff_add_card_inter (fullAgreement dom (u 0) (u 1) z (fam.q z))
          (jointCore dom (u 0) (u 1) H4.1 H4.2)
        have hin := Finset.card_le_card (Finset.inter_subset_right
          (s₁ := fullAgreement dom (u 0) (u 1) z (fam.q z)) (s₂ := jointCore dom (u 0) (u 1) H4.1 H4.2))
        change (freshH4 z).card + _ = _ at hsd'
        omega
      exact (Finset.sum_le_sum hge).trans_eq' (by rw [Finset.sum_const, smul_eq_mul, hGoutCard])
    let Mdoub := T \ P
    have hFourth : 9 * 71582789 ≤ 644245086 + Mdoub.card := by
      have h1 := Finset.card_sdiff_add_card_inter T P
      have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := P))
      change Mdoub.card + _ = T.card at h1; omega
    let remaining (x : I) : Fin 3 := if bm x 1 = false then 0 else if bm x 2 = false then 1 else 2
    let facing (x : I) : Fin 3 := if bm x 1 = false then 1 else 0
    let last (x : I) : F := (u 0 x - H4.1.eval (dom x)) / (H4.2.eval (dom x) - u 1 x)
    let opp (x : I) : F :=
      (u 0 x - (W (remaining x).succ).1.eval (dom x)) / ((W (remaining x).succ).2.eval (dom x) - u 1 x)
    have hMdoubProp {x : I} (hx : x ∈ Mdoub) :
        bm x 0 = false ∧ EighthSaturatedOppositeDirections.count (bm x) = 2 ∧
        last x ∈ Gout ∧ x ∉ jointCore dom (u 0) (u 1) (W (remaining x).succ).1 (W (remaining x).succ).2 ∧
        opp x ∈ pointsOn fam (W (remaining x).succ) ∧
        x ∈ fullAgreement dom (u 0) (u 1) (opp x) (fam.q (opp x)) ∧
        fa + fb * (last x + opp x) + fc * last x * opp x = 0 := by
      obtain ⟨hxT, hxP⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨z0, hz0, hxz0⟩ := Finset.mem_biUnion.mp hxT
      obtain ⟨ha0, ho0⟩ := Finset.mem_sdiff.mp hxz0
      have hb0 : bm x 0 = false := by
        cases h0 : bm x 0
        · rfl
        · exact absurd ((hbmMem x 0).mp h0) ho0
      have hc2 : EighthSaturatedOppositeDirections.count (bm x) = 2 := by
        rcases hreg x with h1 | h2
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1, hb0⟩) hxP
        · exact h2
      obtain ⟨hden0, hlin0, hlast⟩ := hfreshEq (i := 0) (hsubH4 hz0) ha0 ho0
      have hlastEq : last x = z0 := hlast.symm
      have hsum := (count_eq_four_sum (bm x)).symm.trans hc2
      have hremOut : x ∉ jointCore dom (u 0) (u 1) (W (remaining x).succ).1 (W (remaining x).succ).2 := by
        intro hin
        have hbt : bm x (remaining x).succ = true := (hbmMem x (remaining x).succ).mpr hin
        dsimp only [remaining] at hbt
        cases h1 : bm x 1 <;> cases h2 : bm x 2 <;> cases h3 : bm x 3 <;>
          simp [hb0, h1, h2, h3] at hbt hsum
      obtain ⟨z1, hz1, ha1⟩ := hOldSurj (remaining x) x hremOut
      obtain ⟨hden1, hlin1, hopp⟩ := hfreshEq (i := (remaining x).succ) hz1 ha1 hremOut
      have hoppEq : opp x = z1 := hopp.symm
      have hinv : fa + fb * (last x + opp x) + fc * last x * opp x = 0 := by
        have hAg (i : Fin 4) (hi : bm x i = true) :
            (W i).1.eval (dom x) = u 0 x ∧ (W i).2.eval (dom x) = u 1 x := (hbm x i).mp hi
        have hformAt := congrArg (Polynomial.eval (dom x)) (hform (facing x))
        simp only [eval_zero, eval_add, eval_sub, eval_mul, eval_C] at hformAt
        have hfour :
            (FourHeadCoreDeterminant.nearSide (fun i => (W i).2) (facing x)).eval (dom x) ≠ 0 ∧
            (FourHeadCoreDeterminant.farSide (fun i => (W i).2) (facing x)).eval (dom x) ≠ 0 ∧
            (FourHeadCoreDeterminant.nearSide (fun i => (W i).1) (facing x)).eval (dom x) +
              last x * (FourHeadCoreDeterminant.nearSide (fun i => (W i).2) (facing x)).eval (dom x) = 0 ∧
            (FourHeadCoreDeterminant.farSide (fun i => (W i).1) (facing x)).eval (dom x) +
              opp x * (FourHeadCoreDeterminant.farSide (fun i => (W i).2) (facing x)).eval (dom x) = 0 := by
          cases h1 : bm x 1 <;> cases h2 : bm x 2 <;> cases h3 : bm x 3 <;>
            simp [hb0, h1, h2, h3] at hsum
          · have hrem : remaining x = 0 := by simp [remaining, h1]
            have hfac : facing x = 1 := by simp [facing, h1]
            obtain ⟨hu2, hv2⟩ := hAg 2 h2; obtain ⟨hu3, hv3⟩ := hAg 3 h3
            rw [hfac]; simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
              Matrix.cons_val_one, Matrix.cons_val_zero, eval_sub, Fin.succ_one_eq_two,
              hu2, hv2, hu3, hv3]
            rw [hrem] at hden1 hlin1
            simp only [Fin.succ_zero_eq_one] at hden1 hlin1
            exact ⟨fun h => hden0 (by linear_combination -h), fun h => hden1 (by linear_combination -h),
              by rw [hlastEq]; linear_combination -hlin0, by rw [hoppEq]; linear_combination -hlin1⟩
          · have hrem : remaining x = 1 := by simp [remaining, h1, h2]
            have hfac : facing x = 0 := by simp [facing, h1]
            obtain ⟨hu1, hv1⟩ := hAg 1 h1; obtain ⟨hu3, hv3⟩ := hAg 3 h3
            rw [hfac]; simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
              Matrix.cons_val_zero, eval_sub, Fin.succ_zero_eq_one,
              hu1, hv1, hu3, hv3]
            rw [hrem] at hden1 hlin1
            simp only [Fin.succ_one_eq_two] at hden1 hlin1
            exact ⟨fun h => hden0 (by linear_combination -h), fun h => hden1 (by linear_combination -h),
              by rw [hlastEq]; linear_combination -hlin0, by rw [hoppEq]; linear_combination -hlin1⟩
          · have hrem : remaining x = 2 := by simp [remaining, h1, h2]
            have hfac : facing x = 0 := by simp [facing, h1]
            obtain ⟨hu1, hv1⟩ := hAg 1 h1; obtain ⟨hu2, hv2⟩ := hAg 2 h2
            rw [hfac]; simp only [FourHeadCoreDeterminant.nearSide, FourHeadCoreDeterminant.farSide,
              Matrix.cons_val_zero, eval_sub, Fin.succ_zero_eq_one,
              hu1, hv1, hu2, hv2]
            rw [hrem] at hden1 hlin1
            simp only [show (2 : Fin 3).succ = 3 from rfl] at hden1 hlin1
            exact ⟨fun h => hden0 (by linear_combination -h), hden1,
              by rw [hlastEq]; linear_combination -hlin0, by rw [hoppEq]; linear_combination hlin1⟩
        exact EighthSaturatedOppositeDirections.opposite_labels
          hfour.2.2.1 hfour.2.2.2 hfour.1 hfour.2.1 hformAt
      exact ⟨hb0, hc2, hlastEq ▸ hz0, hremOut, hoppEq ▸ hz1, hoppEq ▸ ha1, hinv⟩
    have hOldUniqueSite (k : Fin 3) (z : F) (hz : z ∈ pointsOn fam (W k.succ)) :
        (fullAgreement dom (u 0) (u 1) z (fam.q z) \
          jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2).card ≤ 1 := by
      let freshK (w : F) := fullAgreement dom (u 0) (u 1) w (fam.q w) \
        jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2
      have hdis : ∀ w₁ ∈ pointsOn fam (W k.succ), ∀ w₂ ∈ pointsOn fam (W k.succ), w₁ ≠ w₂ →
          Disjoint (freshK w₁) (freshK w₂) := by
        intro w₁ hw₁ w₂ hw₂ hne
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        obtain ⟨ha₁, ho₁⟩ := Finset.mem_sdiff.mp hx₁
        obtain ⟨ha₂, _⟩ := Finset.mem_sdiff.mp hx₂
        exact hne ((hfreshEq (i := k.succ) hw₁ ha₁ ho₁).2.2.trans
          (hfreshEq (i := k.succ) hw₂ ha₂ ho₁).2.2.symm)
      have hsubAll : (pointsOn fam (W k.succ)).biUnion freshK ⊆
          Finset.univ \ jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2 := by
        intro x hx
        obtain ⟨w, _, hxw⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hxw).2⟩
      have hle := Finset.card_le_card hsubAll
      rw [Finset.card_biUnion (fun w₁ hw₁ w₂ hw₂ hne => hdis w₁ hw₁ w₂ hw₂ hne),
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn] at hle
      have hge1 : ∀ w ∈ pointsOn fam (W k.succ), 1 ≤ (freshK w).card := by
        intro w hw
        obtain ⟨hwG, _⟩ := (mem_pointsOn_iff fam (W k.succ) w).mp hw
        obtain ⟨x, hx1, hx2⟩ := Finset.not_subset.mp
          (not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
            (fullAgreement dom (u 0) (u 1) w (fam.q w))
            (W k.succ).1 (W k.succ).2 (hWdeg k.succ).1 (hWdeg k.succ).2 (fam.noJoint w hwG))
        exact Finset.card_pos.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx1, hx2⟩⟩
      have hsplit := Finset.add_sum_erase (pointsOn fam (W k.succ)) (fun w => (freshK w).card) hz
      have hrest : (pointsOn fam (W k.succ)).card - 1 ≤ ∑ w ∈ (pointsOn fam (W k.succ)).erase z, (freshK w).card := by
        have h := Finset.sum_le_sum (s := (pointsOn fam (W k.succ)).erase z)
          fun w hw => hge1 w (Finset.mem_of_mem_erase hw)
        simpa [Finset.card_erase_of_mem hz] using h
      have hfull := hOldFull k
      have hcoreK : (jointCore dom (u 0) (u 1) (W k.succ).1 (W k.succ).2).card = 357913944 := by
        fin_cases k <;> simp [W, hcaEq, hcbEq, hccEq]
      change (freshK z).card ≤ 1
      dsimp [N] at hle; omega
    have hoppInj : Set.InjOn opp ↑Mdoub := by
      intro x₁ hx₁ x₂ hx₂ heq
      obtain ⟨_, _, _, ho₁, hmem₁, ha₁, _⟩ := hMdoubProp hx₁
      obtain ⟨_, _, _, ho₂, hmem₂, ha₂, _⟩ := hMdoubProp hx₂
      have hk : remaining x₁ = remaining x₂ := by
        by_contra hne
        exact Finset.disjoint_left.mp (hOldDisj hne) hmem₁ (heq ▸ hmem₂)
      have hle1 := hOldUniqueSite (remaining x₁) (opp x₁) hmem₁
      have hx₁m : x₁ ∈ fullAgreement dom (u 0) (u 1) (opp x₁) (fam.q (opp x₁)) \
          jointCore dom (u 0) (u 1) (W (remaining x₁).succ).1 (W (remaining x₁).succ).2 :=
        Finset.mem_sdiff.mpr ⟨ha₁, ho₁⟩
      have hx₂m : x₂ ∈ fullAgreement dom (u 0) (u 1) (opp x₁) (fam.q (opp x₁)) \
          jointCore dom (u 0) (u 1) (W (remaining x₁).succ).1 (W (remaining x₁).succ).2 := by
        rw [hk, heq]; exact Finset.mem_sdiff.mpr ⟨ha₂, ho₂⟩
      exact Finset.card_le_one.mp hle1 x₁ hx₁m x₂ hx₂m
    have hMdoubLe9 : Mdoub.card ≤ 9 := by
      rw [← hGoutCard]
      apply Finset.card_le_card_of_injOn last
      · intro x hx; exact (hMdoubProp hx).2.2.1
      · intro x₁ hx₁ x₂ hx₂ heq
        apply hoppInj hx₁ hx₂
        have h1 := (hMdoubProp hx₁).2.2.2.2.2.2
        have h2 := (hMdoubProp hx₂).2.2.2.2.2.2
        rw [← heq] at h2
        have hnz : fb + fc * last x₁ ≠ 0 := by
          intro h0; apply hdisc
          linear_combination (fb + fc * opp x₁) * h0 - fc * h1
        have hprod : (fb + fc * last x₁) * (opp x₁ - opp x₂) = 0 := by linear_combination h1 - h2
        exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hnz)
    have hcontra := ThreeHeadSuccessorIncidence.nine_double_slots hFourth hMdoubLe9
    omega

/-! ## Unified Dimension-Transfer Brackets & Full 10-Row Successor Table -/

/-- Universal upper bound `mcaDeltaStar ≤ 715,827,882 / 2^30` for every dimension `2 ≤ K ≤ 357,913,941`. -/
theorem successor_upper_bound {K : ℕ} (hKlo : 2 ≤ K) (hKhi : K ≤ 357913941)
    (dom : I ↪ F) (hn : Fintype.card I = N)
    (hB : Fintype.card F / 2 ^ 128 ≤ 2147483648)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)
    mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ≤ ((715827882 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) := by
  classical
  dsimp only
  rw [mcaDeltaStar_interleaved_eq]
  apply mcaDeltaStar_le_of_bad
  let eqv := Fintype.equivFinOfCardEq hn
  let x := eqv.symm.toEmbedding.trans dom
  rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
    eqv.symm x dom (fun _ => rfl)]
  have hsmall := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0 < 2 ^ 128)
  have hq : Fintype.card F ≤ 2 ^ 256 := by omega
  exact ManyHeadLocatorMass.over_budget_128 (h := 0) (d := 2) (r := 357913941) x
    (((715827882 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ)) (by decide) hKlo hKhi (by
      change (1 - (715827882 : ℝ≥0) / 1073741824) * 1073741824 ≤ 357913942
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num)]
      exact tsub_le_iff_right.mpr (by norm_num)) hq (by dsimp [N]; omega)

private theorem bracket_of_top_badCount {Kmax e K : ℕ}
    (hKlo : 2 ≤ K) (hK : K ≤ Kmax) (hKmax : Kmax ≤ 77807386) (he : e ≤ 715827880)
    (dom : I ↪ F) (hn : Fintype.card I = N)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648)
    (hbad : ∀ u : WordStack F (Fin 2) I,
      (canonicalBadScalarRichPointFamily dom (k := Kmax) ((e : ℝ≥0) / (2 ^ 30 : ℕ)) u (by omega)).G.card ≤
        2 ^ 31)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)
    ((e + 1 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ∧
      mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ≤ ((715827882 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) := by
  classical
  have hFge : 2 ^ 31 * 2 ^ 128 ≤ Fintype.card F := by
    have h1 := Nat.mul_div_le (Fintype.card F) (2 ^ 128)
    rw [hB, Nat.mul_comm] at h1; exact h1
  have htop := (safety_of_badCount_le (k := Kmax) (e := e) (by omega) (by omega) dom hn hFge hbad 1).1
  rw [epsMCA_interleaved_eq] at htop
  have hKlt : Kmax < ⌈(1 - (e : ℝ≥0) / (2 ^ 30 : ℕ)) * (Fintype.card I : ℝ≥0)⌉₊ := by
    change Kmax < ⌈(1 - (e : ℝ≥0) / (N : ℕ)) * (Fintype.card I : ℝ≥0)⌉₊
    rw [agreement_ceiling_of_card_eq hn (by decide)]; dsimp only [N]; omega
  have hepsK : epsMCA (F := F) (ReedSolomon.code dom K : Set (I → F)) ((e : ℝ≥0) / (2 ^ 30 : ℕ)) ≤
      1 / (2 : ℝ≥0∞) ^ 128 :=
    (DimensionRaiseMCA.eps_mono_dimension dom (by omega) hK _ hKlt).trans htop
  refine ⟨?_, successor_upper_bound hKlo (by omega) dom hn (by omega) width⟩
  rw [mcaDeltaStar_interleaved_eq]
  let eqv := (Fintype.equivFinOfCardEq hn).symm
  let x : Fin (2 ^ 30) ↪ F := eqv.toEmbedding.trans dom
  rw [ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq
    eqv x dom (fun _ => rfl)]
  have hepsX : epsMCA (F := F) (ReedSolomon.code x K : Set (Fin (2 ^ 30) → F))
      (PrizeShapeRateHalfBracket.predecessorRadius (2 ^ 30) (e + 1)) ≤ 1 / (2 : ℝ≥0∞) ^ 128 := by
    simp only [PrizeShapeRateHalfBracket.predecessorRadius, Nat.add_sub_cancel]
    rwa [← ArkLib.ProximityGap.Frontier.MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq
      eqv x dom (fun _ => rfl)]
  exact PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (a := e + 1) (by omega) (by omega) _ _ hepsX

/-- End-to-end `ThreeHeadResidualSecant` bracket: every `2 ≤ K ≤ 76,695,848` satisfies
`715,827,878 / 2^30 ≤ mcaDeltaStar ≤ 715,827,882 / 2^30`. -/
theorem residual_secant_bracket (hcap : NonlinearComponentCap logDerivPrice)
    {K : ℕ} (hKlo : 2 ≤ K) (hKhi : K ≤ 76695848)
    (dom : I ↪ F) (hn : Fintype.card I = N)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)
    ((715827878 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ∧
      mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ≤ ((715827882 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) := by
  refine bracket_of_top_badCount (Kmax := 76695848) (e := 715827877) hKlo hKhi (by decide)
    (by decide) dom hn hB ?_ width
  intro u
  exact residual_secant_badCount_le hcap _ hn
    (agreement_ceiling_of_card_eq (e := 715827877) hn (by decide)) hchar

/-- Complete ten-row table of `docs/research/proximity-gap/three-head-successor-incidence.md`:
`(Kmax, lowerFirstFailure)`. -/
def successorTable : Fin 10 → ℕ × ℕ :=
  ![(71582790, 715827881),
    (71582792, 715827880),
    (73688168, 715827879),
    (76695850, 715827878),
    (77650737, 715827877),
    (77686751, 715827876),
    (77734913, 715827875),
    (77768622, 715827874),
    (77782879, 715827873),
    (77807386, 715827872)]

/-- End-to-end ten-row `ThreeHeadSuccessorIncidence` bracket theorem: for EVERY row `r : Fin 10`
and EVERY dimension `2 ≤ K ≤ (successorTable r).1`, every injective length-`2^30` domain and every
positive interleaving width satisfies
`(successorTable r).2 / 2^30 ≤ mcaDeltaStar ≤ 715,827,882 / 2^30`,
conditional only on `NonlinearComponentCap logDerivPrice`. -/
theorem successor_table_bracket (hcap : NonlinearComponentCap logDerivPrice)
    (r : Fin 10) {K : ℕ} (hKlo : 2 ≤ K) (hKhi : K ≤ (successorTable r).1)
    (dom : I ↪ F) (hn : Fintype.card I = N)
    (hB : Fintype.card F / 2 ^ 128 = 2147483648)
    (hchar : (2 * 7 - 2) * (2 * tMin - 1) < ringChar F)
    (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code dom K : Set (I → F)) ^⋈ (Fin width)
    ((successorTable r).2 : ℝ≥0) / (2 ^ 30 : ℕ) ≤ mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ∧
      mcaDeltaStar (F := F) C (1 / (2 : ℝ≥0∞) ^ 128) ≤ ((715827882 : ℕ) : ℝ≥0) / (2 ^ 30 : ℕ) := by
  fin_cases r
  · exact bracket_of_top_badCount (Kmax := 71582790) (e := 715827880) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_row1_badCount_le hcap _ hn
        (agreement_ceiling_of_card_eq (e := 715827880) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 71582792) (e := 715827879) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_row2_badCount_le hcap _ hn
        (agreement_ceiling_of_card_eq (e := 715827879) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 73688168) (e := 715827878) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_row3_badCount_le hcap _ hn
        (agreement_ceiling_of_card_eq (e := 715827878) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 76695850) (e := 715827877) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 0 _ hn
        (agreement_ceiling_of_card_eq (e := 715827877) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77650737) (e := 715827876) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 1 _ hn
        (agreement_ceiling_of_card_eq (e := 715827876) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77686751) (e := 715827875) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 2 _ hn
        (agreement_ceiling_of_card_eq (e := 715827875) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77734913) (e := 715827874) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 3 _ hn
        (agreement_ceiling_of_card_eq (e := 715827874) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77768622) (e := 715827873) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 4 _ hn
        (agreement_ceiling_of_card_eq (e := 715827873) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77782879) (e := 715827872) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 5 _ hn
        (agreement_ceiling_of_card_eq (e := 715827872) hn (by decide)) hchar) width
  · exact bracket_of_top_badCount (Kmax := 77807386) (e := 715827871) hKlo hKhi (by decide)
      (by decide) dom hn hB (fun u => successor_moment_cell_badCount_le hcap 6 _ hn
        (agreement_ceiling_of_card_eq (e := 715827871) hn (by decide)) hchar) width

#print axioms successor_row3_badCount_le
#print axioms successor_row2_badCount_le
#print axioms successor_upper_bound
#print axioms residual_secant_bracket
#print axioms successor_table_bracket

end ArkLib.ProximityGap.Frontier.ThreeHeadSuccessorAssembly
