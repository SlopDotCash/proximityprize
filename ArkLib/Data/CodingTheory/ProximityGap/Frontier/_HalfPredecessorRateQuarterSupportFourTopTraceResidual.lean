/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourTopTraceCoupling

/-!
# Rate-quarter support-four: the exact top-trace residual

Fix a support-four line and a codeword whose zero-coordinate trace `A` has size eight.  Every
`t = 6` trace meets `A` in either two or three coordinates.  The two-overlap class has at most one
member: such a trace contains the entire four-point complement of `A`.

The presence of that exceptional two-overlap trace is actually favorable.  Every three-overlap
trace then avoids its two points in `A`.  The three-point parts of the remaining traces therefore
live in a six-point ambient space and have pair intersections at most one.  The constant-weight
Plotkin bound gives at most four of them, and hence at most five `t = 6` codewords in total.

Consequently the condition `#t6 <= 6` is reduced to the homogeneous branch in which every
`t = 6` trace meets the chosen top trace in exactly three points.  The final consumer records this
strictly smaller residual explicitly; it does not assume the original conclusion under another
name.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 100000

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceResidual

open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceCoupling

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Finite-set cores -/

/-- A six-set meeting an eight-set in exactly two points contains the entire four-point
complement in a twelve-point universe. -/
theorem complement_subset_six_of_eight_of_inter_two
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 12) (A B : Finset U)
    (hA : A.card = 8) (hB : B.card = 6)
    (hinter : (A ∩ B).card = 2) :
    Finset.univ \ A ⊆ B := by
  have hKcard : (Finset.univ \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hinter' : (B ∩ A).card = 2 := by
    simpa only [Finset.inter_comm] using hinter
  have hsplit := Finset.card_sdiff_add_card_inter B A
  have hdiffCard : (B \ A).card = 4 := by omega
  have hsub : B \ A ⊆ Finset.univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have heq : B \ A = Finset.univ \ A := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  intro i hi
  have : i ∈ B \ A := by rw [heq]; exact hi
  exact (Finset.mem_sdiff.mp this).1

/-- The three-point parts of two balanced `(3,3)` six-sets meet in at most one point. -/
theorem three_parts_inter_card_le_one
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 12) (A B C : Finset U)
    (hA : A.card = 8) (hB : B.card = 6) (hC : C.card = 6)
    (hBA : (B ∩ A).card = 3) (hCA : (C ∩ A).card = 3)
    (hBC : (B ∩ C).card ≤ 3) :
    ((B ∩ A) ∩ (C ∩ A)).card ≤ 1 := by
  let K := Finset.univ \ A
  have hK : K.card = 4 := by
    rw [show K = Finset.univ \ A by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hBdiff : (B \ A).card = 3 := by
    have hsplit := Finset.card_sdiff_add_card_inter B A
    omega
  have hCdiff : (C \ A).card = 3 := by
    have hsplit := Finset.card_sdiff_add_card_inter C A
    omega
  have hBsub : B \ A ⊆ K := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hCsub : C \ A ⊆ K := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hunion : ((B \ A) ∪ (C \ A)).card ≤ 4 := by
    calc
      ((B \ A) ∪ (C \ A)).card ≤ K.card :=
        Finset.card_le_card (Finset.union_subset hBsub hCsub)
      _ = 4 := hK
  have hout : 2 ≤ ((B \ A) ∩ (C \ A)).card := by
    have hbook := Finset.card_union_add_card_inter (B \ A) (C \ A)
    omega
  let P := (B \ A) ∩ (C \ A)
  let Q := (B ∩ A) ∩ (C ∩ A)
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    have hiNotA := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hiP).1).2
    have hiA := (Finset.mem_inter.mp (Finset.mem_inter.mp hiQ).1).2
    exact hiNotA hiA
  have hsub : P ∪ Q ⊆ B ∩ C := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiP | hiQ
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hiP).1).1,
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hiP).2).1⟩
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hiQ).1).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hiQ).2).1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  change P.card + Q.card ≤ (B ∩ C).card at hcard
  change 2 ≤ P.card at hout
  change Q.card ≤ 1
  omega

/-- Relative to a two-overlap anchor, the three-point part of any balanced six-set lies in the
six-point complement of the anchor inside the top set. -/
theorem three_part_subset_anchor_sdiff
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 12) (A D C : Finset U)
    (hA : A.card = 8) (hD : D.card = 6) (hC : C.card = 6)
    (hAD : (A ∩ D).card = 2) (hCA : (C ∩ A).card = 3)
    (hCD : (C ∩ D).card ≤ 3) :
    C ∩ A ⊆ A \ D := by
  have hKsubD : Finset.univ \ A ⊆ D :=
    complement_subset_six_of_eight_of_inter_two hU A D hA hD hAD
  have hCdiff : (C \ A).card = 3 := by
    have hsplit := Finset.card_sdiff_add_card_inter C A
    omega
  have hCdiffSubD : C \ A ⊆ D := by
    intro x hx
    exact hKsubD (Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩)
  have hthreeCommon : 3 ≤ ((C ∩ D) \ A).card := by
    have hmap : C \ A ⊆ (C ∩ D) \ A := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1,
          hCdiffSubD hx⟩, (Finset.mem_sdiff.mp hx).2⟩
    calc
      3 = (C \ A).card := hCdiff.symm
      _ ≤ ((C ∩ D) \ A).card := Finset.card_le_card hmap
  have hnoA : ((C ∩ D) ∩ A).card = 0 := by
    have hsplit := Finset.card_sdiff_add_card_inter (C ∩ D) A
    omega
  intro i hi
  rw [Finset.mem_sdiff]
  refine ⟨(Finset.mem_inter.mp hi).2, ?_⟩
  intro hiD
  have : i ∈ (C ∩ D) ∩ A := Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hiD⟩,
      (Finset.mem_inter.mp hi).2⟩
  have hpos : 0 < ((C ∩ D) ∩ A).card := Finset.card_pos.mpr ⟨i, this⟩
  omega

open Classical in
/-- A three-point family in a six-point ambient space with pair intersections at most one has
at most four members. -/
theorem three_family_card_le_four_in_six
    {I U : Type} [Fintype I] [Fintype U] [DecidableEq U]
    (V : Finset U) (S : I → Finset U)
    (hV : V.card = 6) (hsub : ∀ i, S i ⊆ V)
    (hsize : ∀ i, (S i).card = 3)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    Fintype.card I ≤ 4 := by
  let R : I → Finset {x : U // x ∈ V} := fun i ↦
    restrictToFinsetSubtype V (S i)
  have hambient : Fintype.card {x : U // x ∈ V} = 6 := by
    simpa only [Fintype.card_coe] using hV
  have hRsize : ∀ i, (R i).card = 3 := by
    intro i
    rw [show R i = restrictToFinsetSubtype V (S i) by rfl,
      restrictToFinsetSubtype_card V (S i) (hsub i), hsize i]
  have hRpair : ∀ i j, i ≠ j → (R i ∩ R j).card ≤ 1 := by
    intro i j hij
    change (restrictToFinsetSubtype V (S i) ∩
      restrictToFinsetSubtype V (S j)).card ≤ 1
    rw [← restrictToFinsetSubtype_inter,
      restrictToFinsetSubtype_card]
    · exact hpair i j hij
    · intro x hx
      exact hsub i (Finset.mem_inter.mp hx).1
  have hplotkin := constantWeight_plotkin_div R 3 1 hRsize hRpair (by
    rw [hambient]
    norm_num)
  norm_num [hambient] at hplotkin
  exact hplotkin

/-! ## The overlap partition -/

/-- The `t = 6` codewords whose trace meets a selected top trace in exactly `r` points. -/
noncomputable def sixTopOverlapStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (top : Fin 16 → F) (r : Nat) : Finset (Fin 16 → F) :=
  (zeroAgreementStratum dom 4 9 u0 u1 6).filter fun c ↦
    (zeroAgreementTrace top u0 u1 ∩ zeroAgreementTrace c u0 u1).card = r

theorem mem_sixTopOverlapStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (top c : Fin 16 → F) (r : Nat) :
    c ∈ sixTopOverlapStratum dom u0 u1 top r ↔
      c ∈ zeroAgreementStratum dom 4 9 u0 u1 6 ∧
        (zeroAgreementTrace top u0 u1 ∩
          zeroAgreementTrace c u0 u1).card = r := by
  simp only [sixTopOverlapStratum, Finset.mem_filter]

/-- Every six-trace meets a chosen eight-trace in either two or three points. -/
theorem six_top_overlap_eq_two_or_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top c : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8)
    (hc : c ∈ zeroAgreementStratum dom 4 9 u0 u1 6) :
    (zeroAgreementTrace top u0 u1 ∩
        zeroAgreementTrace c u0 u1).card = 2 ∨
      (zeroAgreementTrace top u0 u1 ∩
        zeroAgreementTrace c u0 u1).card = 3 := by
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace top u0 u1
  let B : Finset U := zeroAgreementTrace c u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace top u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp htop).2
  have hB : B.card = 6 := by
    rw [show B = zeroAgreementTrace c u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hc).2
  have hunion : (A ∪ B).card ≤ 12 := by
    calc
      (A ∪ B).card ≤ (Finset.univ : Finset U).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 12 := by simp [hU]
  have hlower : 2 ≤ (A ∩ B).card := by
    have hbook := Finset.card_union_add_card_inter A B
    omega
  have htopApp : top ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp htop).1
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hc).1
  have hne : top ≠ c := by
    intro heq
    subst top
    have h8 := (Finset.mem_filter.mp htop).2
    have h6 := (Finset.mem_filter.mp hc).2
    omega
  have hupper : (A ∩ B).card ≤ 3 := by
    simpa only [A, B] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 u1 htopApp hcApp hne
  simpa only [A, B] using (show (A ∩ B).card = 2 ∨ (A ∩ B).card = 3 by omega)

theorem six_stratum_subset_overlap_two_union_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8) :
    zeroAgreementStratum dom 4 9 u0 u1 6 ⊆
      sixTopOverlapStratum dom u0 u1 top 2 ∪
        sixTopOverlapStratum dom u0 u1 top 3 := by
  intro c hc
  rcases six_top_overlap_eq_two_or_three dom u0 u1 hsupport htop hc with htwo | hthree
  · exact Finset.mem_union_left _
      ((mem_sixTopOverlapStratum dom u0 u1 top c 2).mpr ⟨hc, htwo⟩)
  · exact Finset.mem_union_right _
      ((mem_sixTopOverlapStratum dom u0 u1 top c 3).mpr ⟨hc, hthree⟩)

/-! ## The exceptional two-overlap branch -/

open Classical in
/-- There is at most one six-trace meeting the chosen top trace in two points. -/
theorem sixTopOverlapStratum_two_card_le_one
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8) :
    (sixTopOverlapStratum dom u0 u1 top 2).card ≤ 1 := by
  by_contra hnot
  have htwo : 1 < (sixTopOverlapStratum dom u0 u1 top 2).card := by omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp htwo
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace top u0 u1
  let B : Finset U := zeroAgreementTrace c u0 u1
  let C : Finset U := zeroAgreementTrace d u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace top u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp htop).2
  have hcData := (mem_sixTopOverlapStratum dom u0 u1 top c 2).mp hc
  have hdData := (mem_sixTopOverlapStratum dom u0 u1 top d 2).mp hd
  have hB : B.card = 6 := by
    rw [show B = zeroAgreementTrace c u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hcData.1).2
  have hC : C.card = 6 := by
    rw [show C = zeroAgreementTrace d u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hdData.1).2
  have hAB : (A ∩ B).card = 2 := by simpa only [A, B] using hcData.2
  have hAC : (A ∩ C).card = 2 := by simpa only [A, C] using hdData.2
  have hKsubB := complement_subset_six_of_eight_of_inter_two
    hU A B hA hB hAB
  have hKsubC := complement_subset_six_of_eight_of_inter_two
    hU A C hA hC hAC
  have hKcard : (Finset.univ \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hfour : 4 ≤ (B ∩ C).card := by
    rw [← hKcard]
    exact Finset.card_le_card (fun i hi ↦
      Finset.mem_inter.mpr ⟨hKsubB hi, hKsubC hi⟩)
  have hBC : (B ∩ C).card ≤ 3 := by
    simpa only [B, C] using
      zeroAgreementTrace_pair_card_le_three dom u0 u1 6
        hcData.1 hdData.1 hcd
  omega

open Classical in
/-- If a two-overlap anchor exists, the three-overlap class has at most four members. -/
theorem sixTopOverlapStratum_three_card_le_four_of_two_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8)
    (htwo : (sixTopOverlapStratum dom u0 u1 top 2).Nonempty) :
    (sixTopOverlapStratum dom u0 u1 top 3).card ≤ 4 := by
  obtain ⟨anchor, hanchor⟩ := htwo
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace top u0 u1
  let D : Finset U := zeroAgreementTrace anchor u0 u1
  let V : Finset U := A \ D
  let I := {c : Fin 16 → F // c ∈ sixTopOverlapStratum dom u0 u1 top 3}
  let S : I → Finset U := fun c ↦ zeroAgreementTrace c.1 u0 u1 ∩ A
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace top u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp htop).2
  have hanchorData :=
    (mem_sixTopOverlapStratum dom u0 u1 top anchor 2).mp hanchor
  have hD : D.card = 6 := by
    rw [show D = zeroAgreementTrace anchor u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hanchorData.1).2
  have hAD : (A ∩ D).card = 2 := by
    simpa only [A, D] using hanchorData.2
  have hV : V.card = 6 := by
    have hsplit := Finset.card_sdiff_add_card_inter A D
    change (A \ D).card = 6
    omega
  have hsize : ∀ c : I, (S c).card = 3 := by
    intro c
    have hcData := (mem_sixTopOverlapStratum dom u0 u1 top c.1 3).mp c.2
    change (zeroAgreementTrace c.1 u0 u1 ∩ A).card = 3
    simpa only [Finset.inter_comm, A] using hcData.2
  have hsub : ∀ c : I, S c ⊆ V := by
    intro c
    have hcData := (mem_sixTopOverlapStratum dom u0 u1 top c.1 3).mp c.2
    let C : Finset U := zeroAgreementTrace c.1 u0 u1
    have hC : C.card = 6 := by
      rw [show C = zeroAgreementTrace c.1 u0 u1 by rfl,
        zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp hcData.1).2
    have hCA : (C ∩ A).card = 3 := by
      simpa only [C, Finset.inter_comm, A] using hcData.2
    have hcAnchor : c.1 ≠ anchor := by
      intro heq
      subst anchor
      have hthree := hcData.2
      have htwo := hanchorData.2
      omega
    have hCD : (C ∩ D).card ≤ 3 := by
      simpa only [C, D] using
        zeroAgreementTrace_pair_card_le_three dom u0 u1 6
          hcData.1 hanchorData.1 hcAnchor
    change C ∩ A ⊆ A \ D
    exact three_part_subset_anchor_sdiff hU A D C hA hD hC hAD hCA hCD
  have hpair : ∀ c d : I, c ≠ d → (S c ∩ S d).card ≤ 1 := by
    intro c d hcd
    have hcData := (mem_sixTopOverlapStratum dom u0 u1 top c.1 3).mp c.2
    have hdData := (mem_sixTopOverlapStratum dom u0 u1 top d.1 3).mp d.2
    let C : Finset U := zeroAgreementTrace c.1 u0 u1
    let E : Finset U := zeroAgreementTrace d.1 u0 u1
    have hC : C.card = 6 := by
      rw [show C = zeroAgreementTrace c.1 u0 u1 by rfl,
        zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp hcData.1).2
    have hE : E.card = 6 := by
      rw [show E = zeroAgreementTrace d.1 u0 u1 by rfl,
        zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp hdData.1).2
    have hCA : (C ∩ A).card = 3 := by
      simpa only [C, Finset.inter_comm, A] using hcData.2
    have hEA : (E ∩ A).card = 3 := by
      simpa only [E, Finset.inter_comm, A] using hdData.2
    have hCE : (C ∩ E).card ≤ 3 := by
      simpa only [C, E] using
        zeroAgreementTrace_pair_card_le_three dom u0 u1 6
          hcData.1 hdData.1 (fun h ↦ hcd (Subtype.ext h))
    change ((C ∩ A) ∩ (E ∩ A)).card ≤ 1
    exact three_parts_inter_card_le_one hU A C E hA hC hE hCA hEA hCE
  have hpacking := three_family_card_le_four_in_six V S hV hsub hsize hpair
  simpa only [I, Fintype.card_coe] using hpacking

/-- If the exceptional two-overlap class is inhabited, the entire six-stratum has cardinality
at most five. -/
theorem zeroAgreementStratum_six_card_le_five_of_top_two_overlap_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8)
    (htwo : (sixTopOverlapStratum dom u0 u1 top 2).Nonempty) :
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 5 := by
  have hsub := six_stratum_subset_overlap_two_union_three
    dom u0 u1 hsupport htop
  have htwoCap := sixTopOverlapStratum_two_card_le_one
    dom u0 u1 hsupport htop
  have hthreeCap := sixTopOverlapStratum_three_card_le_four_of_two_nonempty
    dom u0 u1 hsupport htop htwo
  calc
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤
        (sixTopOverlapStratum dom u0 u1 top 2 ∪
          sixTopOverlapStratum dom u0 u1 top 3).card :=
      Finset.card_le_card hsub
    _ ≤ (sixTopOverlapStratum dom u0 u1 top 2).card +
        (sixTopOverlapStratum dom u0 u1 top 3).card := Finset.card_union_le _ _
    _ ≤ 5 := by omega

/-! ## The exact homogeneous residual -/

/-- It is enough to bound the homogeneous three-overlap class by six.  The two-overlap branch
already has the stronger total bound five. -/
theorem zeroAgreementStratum_six_card_le_six_of_top_three_overlap_card_le_six
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8)
    (hthree : (sixTopOverlapStratum dom u0 u1 top 3).card ≤ 6) :
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 6 := by
  by_cases htwo : (sixTopOverlapStratum dom u0 u1 top 2).Nonempty
  · exact (zeroAgreementStratum_six_card_le_five_of_top_two_overlap_nonempty
      dom u0 u1 hsupport htop htwo).trans (by omega)
  · have htwoEmpty : sixTopOverlapStratum dom u0 u1 top 2 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp htwo
    have hsub := six_stratum_subset_overlap_two_union_three
      dom u0 u1 hsupport htop
    rw [htwoEmpty, Finset.empty_union] at hsub
    exact (Finset.card_le_card hsub).trans hthree

/-- Conditional closure of the top branch using only the homogeneous three-overlap residual. -/
theorem lineBadScalars_card_le_sixteen_of_top_three_overlap_card_le_six
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4)
    {top : Fin 16 → F}
    (htop : top ∈ zeroAgreementStratum dom 4 9 u0 u1 8)
    (hthree : (sixTopOverlapStratum dom u0 u1 top 3).card ≤ 6) :
    (lineBadScalars dom 4 9 u0 u1).card ≤ 16 := by
  have hsix := zeroAgreementStratum_six_card_le_six_of_top_three_overlap_card_le_six
    dom u0 u1 hsupport htop hthree
  exact lineBadScalars_card_le_sixteen_of_support_four_of_eight_nonempty_of_six_card_le_six
    dom u0 u1 hsafe hsupport ⟨top, htop⟩ hsix

#print axioms sixTopOverlapStratum_two_card_le_one
#print axioms sixTopOverlapStratum_three_card_le_four_of_two_nonempty
#print axioms zeroAgreementStratum_six_card_le_five_of_top_two_overlap_nonempty
#print axioms zeroAgreementStratum_six_card_le_six_of_top_three_overlap_card_le_six
#print axioms lineBadScalars_card_le_sixteen_of_top_three_overlap_card_le_six

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceResidual
