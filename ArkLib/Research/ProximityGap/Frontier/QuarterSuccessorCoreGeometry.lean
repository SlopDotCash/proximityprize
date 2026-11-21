/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorThreeHeads
import ArkLib.Research.ProximityGap.Frontier._P1RateQuarterCommonFactorOneStepNoGo
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity

/-! # Every bad scalar at an over-budget quarter-rate successor lies on one of three heads -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorCoreGeometry
open Finset Polynomial Code HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterComplementaryCores
open HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterDeterminantMultiplicity
open scoped NNReal

private theorem outside_sum {I : Type} [Fintype I] [DecidableEq I] (A B C S : Finset I) :
    (A \ S).card + (B \ S).card + (C \ S).card ≤
      2 * (Fintype.card I - S.card) + (A ∩ B ∩ C).card := by
  let a := A \ S
  let b := B \ S
  let c := C \ S
  have lim (T : Finset I) (h : T ⊆ Sᶜ) : T.card ≤ Fintype.card I - S.card :=
    (card_le_card h).trans_eq (card_compl S)
  have sub (T : Finset I) : T \ S ⊆ Sᶜ := fun _ h => mem_compl.mpr (mem_sdiff.mp h).2
  have h₁ := lim (a ∪ b) (union_subset (sub A) (sub B))
  have h₂ := lim ((a ∩ b) ∪ c) (union_subset (inter_subset_left.trans (sub A)) (sub C))
  have h₃ := card_le_card (show a ∩ b ∩ c ⊆ A ∩ B ∩ C from
    inter_subset_inter (inter_subset_inter sdiff_subset sdiff_subset) sdiff_subset)
  have ab := card_union_add_card_inter a b
  have abc := card_union_add_card_inter (a ∩ b) c
  change a.card + b.card + c.card ≤ _
  omega

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Finite F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- An over-budget pair yields exactly three distinct polynomial secants carrying all
genuine bad scalars. The total shortfall in the three pair overlaps, uncovered sites,
triple coincidences and surplus core lengths is exactly seven. -/
theorem actual_full_cover {p : ℕ} [CharP F p] (hp : 132 < p)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396) (hG : 1073741824 < fam.G.card) :
    ∃ a b c : LineParameter F, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (∀ h ∈ ({a,b,c} : Finset _), h ∈ lineParameters fam ∧ 178956951 ≤ (pointsOn fam h).card) ∧
      threeLineDeterminant a b c = 0 ∧
      fam.G = pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ∧
      let A := jointCore dom (u 0) (u 1) a.1 a.2
      let B := jointCore dom (u 0) (u 1) b.1 b.2
      let C := jointCore dom (u 0) (u 1) c.1 c.2
      626349394 ≤ A.card ∧ 626349394 ≤ B.card ∧ 626349394 ≤ C.card ∧
      (A ∪ B ∪ C)ᶜ.card + (A ∩ B ∩ C).card + (268435455 - (A ∩ B).card) +
        (268435455 - (A ∩ C).card) + (268435455 - (B ∩ C).card) +
        (A.card - 626349394) + (B.card - 626349394) + (C.card - 626349394) = 7 := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨E, H, _, h3, _, hline⟩ := QuarterSuccessorThreeHeads.actual_heads hp fam hn ht hG
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp h3
  let D (h : LineParameter F) := jointCore dom (u 0) (u 1) h.1 h.2
  have ha := hline a (by simp)
  have hb := hline b (by simp)
  have hc := hline c (by simp)
  have near (h : LineParameter F) (hh : h ∈ lineParameters fam)
      (hh' : 178956951 ≤ (pointsOn fam h).card) :
      626349394 ≤ (D h).card := by
    have size := pointsOn_card_mul_max_add_core_le fam hh
    rw [ht,hn] at size
    change (pointsOn fam h).card * max 1 (626349396 - (D h).card) + (D h).card ≤ 1073741824 at size
    have low := Nat.mul_le_mul hh' (Nat.le_max_right 1 (626349396 - (D h).card))
    omega
  have hA := near a ha.1 ha.2
  have hB := near b hb.1 hb.2
  have hC := near c hc.1 hc.2
  have ov {x y : LineParameter F} (hx : x ∈ lineParameters fam) (hy : y ∈ lineParameters fam)
      (hne : x ≠ y) : (D x ∩ D y).card ≤ 268435455 :=
    jointCore_inter_card_le_degree_pred fam (by decide) hx hy hne
  have oab := ov ha.1 hb.1 hab
  have oac := ov ha.1 hc.1 hac
  have obc := ov hb.1 hc.1 hbc
  have ex := P1RateQuarterCommonFactorOneStepNoGo.card_three_union_add_pair_inters_eq
    (D a) (D b) (D c)
  have un := (card_le_univ (D a ∪ D b ∪ D c)).trans_eq hn
  have triple : (D a ∩ D b ∩ D c).card ≤ 7 := by omega
  have det := threeLineDeterminant_eq_zero_of_jointCore_card_sum_sub_domain_gt dom (u 0) (u 1)
    a b c (lineParameter_degree_lt fam ha.1).1 (lineParameter_degree_lt fam ha.1).2
    (lineParameter_degree_lt fam hb.1).1 (lineParameter_degree_lt fam hb.1).2
    (lineParameter_degree_lt fam hc.1).1 (lineParameter_degree_lt fam hc.1).2 (by
      change 2 * 268435456 - 2 < (D a).card + (D b).card + (D c).card - Fintype.card I
      omega)
  refine ⟨a,b,c,hab,hac,hbc,hline, det, ?_, hA, hB, hC, ?_⟩
  · apply Subset.antisymm
    · intro z hz
      by_contra hbad
      let S := fullAgreement dom (u 0) (u 1) z (fam.q z)
      have big : 626349396 ≤ S.card := ht ▸ fam.threshold_le z hz
      have off (h : LineParameter F) (hh : h ∈ lineParameters fam) (hh' : z ∉ pointsOn fam h) :
          (D h ∩ S).card ≤ 268435455 := by
        obtain ⟨hu,hv⟩ := lineParameter_degree_lt fam hh
        rw [inter_comm]
        exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) (by decide)
          (fam.degree_lt z hz) hu hv (fun eq => hh' ((mem_pointsOn_iff fam h z).mpr ⟨hz,eq⟩))
      have sa := off a ha.1 (fun eq => hbad (mem_union_left _ (mem_union_left _ eq)))
      have sb := off b hb.1 (fun eq => hbad (mem_union_left _ (mem_union_right _ eq)))
      have sc := off c hc.1 (fun eq => hbad (mem_union_right _ eq))
      have out := outside_sum (D a) (D b) (D c) S
      rw [hn] at out
      have aS := card_sdiff_add_card_inter (D a) S
      have bS := card_sdiff_add_card_inter (D b) S
      have cS := card_sdiff_add_card_inter (D c) S
      omega
    · exact union_subset (union_subset (pointsOn_subset_G fam a) (pointsOn_subset_G fam b))
        (pointsOn_subset_G fam c)
  · change (D a ∪ D b ∪ D c)ᶜ.card + (D a ∩ D b ∩ D c).card +
      (268435455 - (D a ∩ D b).card) + (268435455 - (D a ∩ D c).card) +
      (268435455 - (D b ∩ D c).card) + ((D a).card - 626349394) +
      ((D b).card - 626349394) + ((D c).card - 626349394) = 7
    rw [card_compl,hn]
    omega

end ArkLib.ProximityGap.Frontier.QuarterSuccessorCoreGeometry
