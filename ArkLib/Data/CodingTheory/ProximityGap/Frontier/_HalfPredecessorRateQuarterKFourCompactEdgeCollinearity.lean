/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleCollinearity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSignatures

/-!
# Rate-quarter `k = 4`: compact missed edges force one decoded line

Three regular outsiders whose missed edges cover at most four coordinates
have at least four common fresh agreements.  The degree-three triple root cap
therefore makes the third decoded polynomial point collinear with the first
two.  If this compact-union condition holds against two fixed outsiders, the
whole regular population lies on their secant.

At length sixteen and threshold nine, five points on one relevant line force
an eight-coordinate core.  Consequently a unique-eight-core residual cannot
carry such a compact missed-edge population: uniqueness would identify the
new secant with the source line, contradicting regular outsider membership.

Both quotient degeneracies feed this consumer.  A repeated missed edge is
compact trivially, while three two-edges through one fixed coordinate cover
at most four coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

attribute [local instance] Classical.propDecidable

/-! ## Finite compactness -/

variable {U : Type*} [DecidableEq U]

/-- Three two-subsets through one common coordinate cover at most four
coordinates. -/
theorem three_pairs_union_card_le_four_of_common_mem
    (A B C : Finset U) (key : U)
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2)
    (hkeyA : key ∈ A) (hkeyB : key ∈ B) (hkeyC : key ∈ C) :
    (A ∪ B ∪ C).card ≤ 4 := by
  let R : Finset U :=
    {key} ∪ (A.erase key ∪ B.erase key ∪ C.erase key)
  have hsub : A ∪ B ∪ C ⊆ R := by
    intro x hx
    simp only [Finset.mem_union] at hx
    by_cases hxkey : x = key
    · subst x
      exact Finset.mem_union_left _ (Finset.mem_singleton_self key)
    · apply Finset.mem_union_right
      rcases hx with (hxA | hxB) | hxC
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxkey, hxA⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxkey, hxB⟩))
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxkey, hxC⟩)
  have hAe : (A.erase key).card = 1 := by
    rw [Finset.card_erase_of_mem hkeyA, hA]
  have hBe : (B.erase key).card = 1 := by
    rw [Finset.card_erase_of_mem hkeyB, hB]
  have hCe : (C.erase key).card = 1 := by
    rw [Finset.card_erase_of_mem hkeyC, hC]
  have hRcard : R.card ≤ 4 := by
    calc
      R.card ≤ ({key} : Finset U).card +
          (A.erase key ∪ B.erase key ∪ C.erase key).card :=
        Finset.card_union_le _ _
      _ ≤ 1 + ((A.erase key ∪ B.erase key).card +
          (C.erase key).card) := by
        have habc := Finset.card_union_le
          (A.erase key ∪ B.erase key) (C.erase key)
        simpa only [Finset.card_singleton] using Nat.add_le_add_left habc 1
      _ ≤ 1 + (((A.erase key).card + (B.erase key).card) +
          (C.erase key).card) := by
        have hab := Finset.card_union_le (A.erase key) (B.erase key)
        omega
      _ = 4 := by rw [hAe, hBe, hCe]
  exact (Finset.card_le_card hsub).trans hRcard

/-! ## Compact edges imply collinearity -/

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Three prescribed regular outsiders are collinear whenever their missed
edges cover at most four coordinates. -/
theorem third_regular_mem_pointsOn_secant_of_missed_union_card_le_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hunion :
      (regularMissedEdge family line gamma1 ∪
        regularMissedEdge family line gamma2 ∪
        regularMissedEdge family line gamma3).card ≤ 4) :
    gamma3 ∈ pointsOn family (secantParameter family gamma1 gamma2) := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
  let R : Finset I := V \ (E1 ∪ E2 ∪ E3)
  let A : F → Finset I := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  have hVcard : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hEsub : E1 ∪ E2 ∪ E3 ⊆ V := by
    apply Finset.union_subset
    · apply Finset.union_subset <;> intro i hi
      · exact (Finset.mem_sdiff.mp hi).1
      · exact (Finset.mem_sdiff.mp hi).1
    · intro i hi
      exact (Finset.mem_sdiff.mp hi).1
  have hRcard : 4 ≤ R.card := by
    have hsplit := Finset.card_sdiff_add_card_inter V (E1 ∪ E2 ∪ E3)
    have hinter : V ∩ (E1 ∪ E2 ∪ E3) = E1 ∪ E2 ∪ E3 :=
      Finset.inter_eq_right.mpr hEsub
    rw [hinter, hVcard] at hsplit
    change R.card + (E1 ∪ E2 ∪ E3).card = 8 at hsplit
    change (E1 ∪ E2 ∪ E3).card ≤ 4 at hunion
    omega
  have hRsub : R ⊆ (A gamma1 ∩ A gamma2) ∩ A gamma3 := by
    intro i hi
    have hiData := Finset.mem_sdiff.mp hi
    have hiV : i ∈ V := hiData.1
    have hiNot := hiData.2
    have hiFresh : ∀ gamma E,
        E = regularMissedEdge family line gamma →
        i ∉ E → i ∈ sourceFreshAgreement family line gamma := by
      intro gamma E hE hiE
      by_contra hiS
      apply hiE
      rw [hE]
      exact Finset.mem_sdiff.mpr ⟨hiV, hiS⟩
    have hi1 : i ∈ sourceFreshAgreement family line gamma1 :=
      hiFresh gamma1 E1 rfl (fun hiE1 => hiNot (by simp [hiE1]))
    have hi2 : i ∈ sourceFreshAgreement family line gamma2 :=
      hiFresh gamma2 E2 rfl (fun hiE2 => hiNot (by simp [hiE2]))
    have hi3 : i ∈ sourceFreshAgreement family line gamma3 :=
      hiFresh gamma3 E3 rfl (fun hiE3 => hiNot (by simp [hiE3]))
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_inter.mpr ?_, (Finset.mem_sdiff.mp hi3).1⟩
    exact ⟨(Finset.mem_sdiff.mp hi1).1, (Finset.mem_sdiff.mp hi2).1⟩
  have htriple : 3 < ((A gamma1 ∩ A gamma2) ∩ A gamma3).card :=
    lt_of_lt_of_le (by omega) (Finset.card_le_card hRsub)
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  have hgamma1G :=
    (mem_outsideLine_iff family line gamma1).mp hgamma1Data.1 |>.1
  have hgamma2G :=
    (mem_outsideLine_iff family line gamma2).mp hgamma2Data.1 |>.1
  have hgamma3G :=
    (mem_outsideLine_iff family line gamma3).mp hgamma3Data.1 |>.1
  have hslope :
      slopePolynomial gamma1 gamma2 (family.q gamma1) (family.q gamma2) =
        slopePolynomial gamma1 gamma3 (family.q gamma1) (family.q gamma3) := by
    by_contra hslopeNe
    have hupper := triple_fullAgreement_card_le_pred_of_slope_ne
      dom (u 0) (u 1) (k := 4) (by norm_num) h12 h13
        (family.degree_lt gamma1 hgamma1G)
        (family.degree_lt gamma2 hgamma2G)
        (family.degree_lt gamma3 hgamma3G) hslopeNe
    change ((A gamma1 ∩ A gamma2) ∩ A gamma3).card ≤ 4 - 1 at hupper
    norm_num only at hupper
    exact (Nat.not_lt_of_ge hupper htriple).elim
  have hthird := third_point_on_secant_line_of_slope_eq h13 hslope.symm
  exact (mem_pointsOn_iff family
      (secantParameter family gamma1 gamma2) gamma3).mpr
    ⟨hgamma3G, by simpa only [secantParameter] using hthird⟩

/-- A compact missed-edge population lies on the secant through two fixed
regular outsiders. -/
theorem regularOutsideLine_subset_pointsOn_secant_of_compact_missed_edges
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma1 gamma2 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (h12 : gamma1 ≠ gamma2)
    (hcompact : ∀ theta ∈ regularOutsideLine family line,
      (regularMissedEdge family line gamma1 ∪
        regularMissedEdge family line gamma2 ∪
        regularMissedEdge family line theta).card ≤ 4) :
    regularOutsideLine family line ⊆
      pointsOn family (secantParameter family gamma1 gamma2) := by
  intro theta htheta
  by_cases htheta1 : theta = gamma1
  · subst theta
    have hgamma1Data := hgamma1
    simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
    exact first_point_mem_pointsOn_secant family
      ((mem_outsideLine_iff family line gamma1).mp hgamma1Data.1 |>.1)
  by_cases htheta2 : theta = gamma2
  · subst theta
    have hgamma2Data := hgamma2
    simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
    exact second_point_mem_pointsOn_secant family
      ((mem_outsideLine_iff family line gamma2).mp hgamma2Data.1 |>.1) h12
  exact third_regular_mem_pointsOn_secant_of_missed_union_card_le_four
    family hn hcore hgamma1 hgamma2 htheta h12 (Ne.symm htheta1)
      (hcompact theta htheta)

/-! ## Five points force an eight-core -/

/-- At length sixteen and threshold at least nine, five points on one
relevant decoded line force its core to have size at least eight. -/
theorem eight_le_core_of_five_le_pointsOn
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hfive : 5 ≤ (pointsOn family line).card) :
    8 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let L := (pointsOn family line).card
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  change L * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) + z ≤
    Fintype.card I at hpack
  have hfactor : 9 - z ≤ max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) :=
    (Nat.sub_le_sub_right hthreshold z).trans (le_max_right _ _)
  have hmul : 5 * (9 - z) ≤ L * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) :=
    Nat.mul_le_mul hfive hfactor
  have hbase : 5 * (9 - z) + z ≤ Fintype.card I :=
    (Nat.add_le_add_right hmul z).trans hpack
  rw [hn] at hbase
  change 8 ≤ z
  by_contra hnot
  omega

/-- The unique-eight-core residual is incompatible with a compact regular
missed-edge population. -/
theorem uniqueEightCoreResidual_false_of_compact_missed_edges
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (residual : UniqueEightCoreResidual family)
    {gamma1 gamma2 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family residual.source)
    (hgamma2 : gamma2 ∈ regularOutsideLine family residual.source)
    (h12 : gamma1 ≠ gamma2)
    (hcompact : ∀ theta ∈ regularOutsideLine family residual.source,
      (regularMissedEdge family residual.source gamma1 ∪
        regularMissedEdge family residual.source gamma2 ∪
        regularMissedEdge family residual.source theta).card ≤ 4) :
    False := by
  let line2 := secantParameter family gamma1 gamma2
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data hgamma2Data
  have hgamma1Out :=
    (mem_outsideLine_iff family residual.source gamma1).mp hgamma1Data.1
  have hgamma2Out :=
    (mem_outsideLine_iff family residual.source gamma2).mp hgamma2Data.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgamma1Out.1 hgamma2Out.1 h12
  have hsub : regularOutsideLine family residual.source ⊆
      pointsOn family line2 := by
    simpa only [line2] using
      regularOutsideLine_subset_pointsOn_secant_of_compact_missed_edges
        family hn residual.source_core_card hgamma1 hgamma2 h12 hcompact
  have hpoints : 5 ≤ (pointsOn family line2).card := by
    have hcard := Finset.card_le_card hsub
    have height := residual.eight_regular_outsiders
    have hlower : 5 ≤
        (regularOutsideLine family residual.source).card := by omega
    exact hlower.trans hcard
  have hcore : 8 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card :=
    eight_le_core_of_five_le_pointsOn family hn hthreshold hline2 hpoints
  have hlineEq : line2 = residual.source :=
    residual.source_unique line2 hline2 hcore
  have hgamma1On : gamma1 ∈ pointsOn family line2 := hsub hgamma1
  have hgamma1Source : gamma1 ∈ pointsOn family residual.source := by
    simpa only [hlineEq] using hgamma1On
  exact hgamma1Out.2
    ((mem_pointsOn_iff family residual.source gamma1).mp hgamma1Source |>.2)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity
#print axioms three_pairs_union_card_le_four_of_common_mem
#print axioms third_regular_mem_pointsOn_secant_of_missed_union_card_le_four
#print axioms regularOutsideLine_subset_pointsOn_secant_of_compact_missed_edges
#print axioms eight_le_core_of_five_le_pointsOn
#print axioms uniqueEightCoreResidual_false_of_compact_missed_edges
