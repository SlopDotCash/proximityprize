/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleCollinearity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

/-!
# Rate-quarter `n = 16`, `k = 4`: cross triples under a unique core

This file consumes cross-root-triple collinearity inside the unique-eight-core
residual.  The second-eight-core branch is excluded by uniqueness.  The
remaining cross-triple secant has core size six or seven.

Its overlap with the source core cannot be three.  At overlap three, all
three collinear regular outsiders have the same source-root triple.  Regular
signature rigidity then forces another eight-core meeting the source in
three coordinates, contradicting uniqueness of the source eight-core.

Complementary-core closure supplies the remaining exact arithmetic:

* a six-core has source overlap one or two and leaves four or three holes;
* a seven-core has source overlap exactly two and leaves exactly three holes.

Finally, for any source-eight/core-seven pair with overlap two, every
selected point off both lines must agree on all three holes.  Its agreement
inside either core is at most three; the threshold-nine lower bound therefore
forces saturation on the uncovered coordinates.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleCollinearity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- If a regular outsider lies on a target line and the target/source core
intersection has size three, that intersection is exactly the outsider's
three-coordinate source-root signature. -/
theorem source_target_core_inter_eq_regularRootTriple_of_overlap_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (source target : LineParameter F)
    (hsourceCore :
      (jointCore dom (u 0) (u 1) source.1 source.2).card = 8)
    {theta : F} (htheta : theta ∈ regularOutsideLine family source)
    (hthetaOn : theta ∈ pointsOn family target)
    (hinter :
      (jointCore dom (u 0) (u 1) source.1 source.2 ∩
        jointCore dom (u 0) (u 1) target.1 target.2).card = 3) :
    jointCore dom (u 0) (u 1) source.1 source.2 ∩
        jointCore dom (u 0) (u 1) target.1 target.2 =
      regularRootTriple family source theta := by
  have hthetaEq := (mem_pointsOn_iff family target theta).mp hthetaOn |>.2
  have hsub :
      jointCore dom (u 0) (u 1) source.1 source.2 ∩
          jointCore dom (u 0) (u 1) target.1 target.2 ⊆
        regularRootTriple family source theta := by
    intro i hi
    have hiData := Finset.mem_inter.mp hi
    have hiTarget : i ∈
        fullAgreement dom (u 0) (u 1) theta
          (target.1 + C theta * target.2) :=
      jointCore_subset_fullAgreement
        dom (u 0) (u 1) target.1 target.2 theta hiData.2
    simp only [regularRootTriple, Finset.mem_inter]
    refine ⟨?_, hiData.1⟩
    rw [hthetaEq]
    exact hiTarget
  apply Finset.eq_of_subset_of_card_le hsub
  have hrootCard :=
    (regular_signature_cardinalities family hn hsourceCore htheta).1
  omega

/-- The complete cross-triple package surviving under a unique source
eight-core. -/
structure UniqueCoreCrossTripleResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) where
  gamma1 : F
  gamma1_regular : gamma1 ∈ regularOutsideLine family residual.source
  gamma2 : F
  gamma2_regular : gamma2 ∈ regularOutsideLine family residual.source
  gamma3 : F
  gamma3_regular : gamma3 ∈ regularOutsideLine family residual.source
  gamma12 : gamma1 ≠ gamma2
  gamma13 : gamma1 ≠ gamma3
  gamma23 : gamma2 ≠ gamma3
  compact_missed_union :
    (regularMissedEdge family residual.source gamma1 ∪
      regularMissedEdge family residual.source gamma2 ∪
      regularMissedEdge family residual.source gamma3).card ≤ 4
  secant_mem : secantParameter family gamma1 gamma2 ∈ lineParameters family
  secant_ne_source : secantParameter family gamma1 gamma2 ≠ residual.source
  gamma3_on_secant : gamma3 ∈ pointsOn family
    (secantParameter family gamma1 gamma2)
  secant_core_card :
    (jointCore dom (u 0) (u 1)
      (secantParameter family gamma1 gamma2).1
      (secantParameter family gamma1 gamma2).2).card = 6 ∨
    (jointCore dom (u 0) (u 1)
      (secantParameter family gamma1 gamma2).1
      (secantParameter family gamma1 gamma2).2).card = 7
  source_secant_inter_card_le_two :
    (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2 ∩
      jointCore dom (u 0) (u 1)
        (secantParameter family gamma1 gamma2).1
        (secantParameter family gamma1 gamma2).2).card ≤ 2
  uncovered_balance :
    (Finset.univ \ (
      jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
        jointCore dom (u 0) (u 1)
          (secantParameter family gamma1 gamma2).1
          (secantParameter family gamma1 gamma2).2)).card +
      (jointCore dom (u 0) (u 1)
        (secantParameter family gamma1 gamma2).1
        (secantParameter family gamma1 gamma2).2).card =
      8 +
        (jointCore dom (u 0) (u 1)
            residual.source.1 residual.source.2 ∩
          jointCore dom (u 0) (u 1)
            (secantParameter family gamma1 gamma2).1
            (secantParameter family gamma1 gamma2).2).card
  core_six_data :
    (jointCore dom (u 0) (u 1)
      (secantParameter family gamma1 gamma2).1
      (secantParameter family gamma1 gamma2).2).card = 6 →
      ((jointCore dom (u 0) (u 1)
          residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1)
          (secantParameter family gamma1 gamma2).1
          (secantParameter family gamma1 gamma2).2).card = 1 ∧
        (Finset.univ \ (
          jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
            jointCore dom (u 0) (u 1)
              (secantParameter family gamma1 gamma2).1
              (secantParameter family gamma1 gamma2).2)).card = 3) ∨
      ((jointCore dom (u 0) (u 1)
          residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1)
          (secantParameter family gamma1 gamma2).1
          (secantParameter family gamma1 gamma2).2).card = 2 ∧
        (Finset.univ \ (
          jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
            jointCore dom (u 0) (u 1)
              (secantParameter family gamma1 gamma2).1
              (secantParameter family gamma1 gamma2).2)).card = 4)
  core_seven_data :
    (jointCore dom (u 0) (u 1)
      (secantParameter family gamma1 gamma2).1
      (secantParameter family gamma1 gamma2).2).card = 7 →
      (jointCore dom (u 0) (u 1)
          residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1)
          (secantParameter family gamma1 gamma2).1
          (secantParameter family gamma1 gamma2).2).card = 2 ∧
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
          jointCore dom (u 0) (u 1)
            (secantParameter family gamma1 gamma2).1
            (secantParameter family gamma1 gamma2).2)).card = 3

/-- **Cross-triple synthesis in a counterexample.**  The forced secant core
has exactly the overlap/hole alternatives recorded above. -/
theorem exists_uniqueCoreCrossTripleResidual_of_card_gt_sixteen
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    (residual : UniqueEightCoreResidual family) :
    Nonempty (UniqueCoreCrossTripleResidual family residual) := by
  have hn' : Fintype.card I = 2 * 8 := by omega
  have hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8 := by
    intro line hline
    exact relevant_core_card_le_eight_of_card_gt_sixteen
      family hn hthreshold.ge hcard hline
  rcases exists_second_eight_core_or_crossTriple_six_seven_core
      family hn hthreshold.ge residual.source_core_card hcoreCap
        residual.eight_regular_outsiders with hsecond | hcross
  · obtain ⟨line2, hline2, hlineNe, hcore2⟩ := hsecond
    exact (hlineNe
      (residual.source_unique line2 hline2 (by omega))).elim
  · obtain ⟨gamma1, hgamma1, gamma2, hgamma2, gamma3, hgamma3,
      h12, h13, h23, hcompact, hrest⟩ := hcross
    dsimp only at hrest
    obtain ⟨hline2, hlineNe, hgamma3On, hcoreCases⟩ := hrest
    let line2 := secantParameter family gamma1 gamma2
    let D := jointCore dom (u 0) (u 1)
      residual.source.1 residual.source.2
    let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
    let H := Finset.univ \ (D ∪ D2)
    have hgamma1Data := hgamma1
    have hgamma2Data := hgamma2
    simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data hgamma2Data
    have hgamma1G :=
      (mem_outsideLine_iff family residual.source gamma1).mp
        hgamma1Data.1 |>.1
    have hgamma2G :=
      (mem_outsideLine_iff family residual.source gamma2).mp
        hgamma2Data.1 |>.1
    have hgamma1On : gamma1 ∈ pointsOn family line2 :=
      first_point_mem_pointsOn_secant family hgamma1G
    have hgamma2On : gamma2 ∈ pointsOn family line2 :=
      second_point_mem_pointsOn_secant family hgamma2G h12
    have hinterCap : (D ∩ D2).card ≤ 3 := by
      simpa only [D, D2, line2] using
        (relevant_jointCore_inter_card_le_three_of_distinct
          family residual.source_mem hline2 hlineNe.symm)
    have hinterLeTwo : (D ∩ D2).card ≤ 2 := by
      by_contra hnot
      have hinterThree : (D ∩ D2).card = 3 := by omega
      have hroot1 :=
        source_target_core_inter_eq_regularRootTriple_of_overlap_three
          family hn residual.source line2 residual.source_core_card
            hgamma1 hgamma1On
            (by simpa only [D, D2] using hinterThree)
      have hroot2 :=
        source_target_core_inter_eq_regularRootTriple_of_overlap_three
          family hn residual.source line2 residual.source_core_card
            hgamma2 hgamma2On
            (by simpa only [D, D2] using hinterThree)
      have hroot3 :=
        source_target_core_inter_eq_regularRootTriple_of_overlap_three
          family hn residual.source line2 residual.source_core_card
            hgamma3 hgamma3On
            (by simpa only [D, D2] using hinterThree)
      have hroot12 : regularRootTriple family residual.source gamma1 =
          regularRootTriple family residual.source gamma2 :=
        hroot1.symm.trans hroot2
      have hroot13 : regularRootTriple family residual.source gamma1 =
          regularRootTriple family residual.source gamma3 :=
        hroot1.symm.trans hroot3
      obtain ⟨line3, hline3, hcore3, hinter3⟩ :=
        exists_overlap_three_core_eq_eight_of_three_regular_same_rootTriple
          family hn residual.source_mem residual.source_core_card hcoreCap
            hgamma1 hgamma2 hgamma3 h12 h13 h23 hroot12 hroot13
      have hline3Eq : line3 = residual.source :=
        residual.source_unique line3 hline3 (by omega)
      rw [hline3Eq] at hinter3
      have hbad : (D ∩ D).card = 3 := by
        simpa only [D] using hinter3
      rw [Finset.inter_self, show D.card = 8 by
        simpa only [D] using residual.source_core_card] at hbad
      omega
    have hDcard : D.card = 8 := by
      simpa only [D] using residual.source_core_card
    have hHbalance : H.card + D2.card = 8 + (D ∩ D2).card := by
      have hunionInter := Finset.card_union_add_card_inter D D2
      have hcomplement : H.card = 16 - (D ∪ D2).card := by
        simp only [H, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, hn]
      have hunionLe : (D ∪ D2).card ≤ 16 := by
        have := Finset.card_le_univ (D ∪ D2)
        simpa only [Finset.card_univ, hn] using this
      omega
    have hthreeHoles : 3 ≤ H.card := by
      by_contra hnot
      have hmissing : H.card ≤ 2 := by omega
      have hle := card_le_two_mul_of_saturated_small_complement
        family (k := 4) (h := 8) (by norm_num) (by norm_num)
          hn' hthreshold.ge residual.source line2 residual.source_mem
            hline2 (by simpa only [H, D, D2] using hmissing)
      norm_num at hle
      omega
    have hsix : D2.card = 6 →
        ((D ∩ D2).card = 1 ∧ H.card = 3) ∨
          ((D ∩ D2).card = 2 ∧ H.card = 4) := by
      intro hD2
      omega
    have hseven : D2.card = 7 →
        (D ∩ D2).card = 2 ∧ H.card = 3 := by
      intro hD2
      omega
    exact ⟨{
      gamma1 := gamma1
      gamma1_regular := hgamma1
      gamma2 := gamma2
      gamma2_regular := hgamma2
      gamma3 := gamma3
      gamma3_regular := hgamma3
      gamma12 := h12
      gamma13 := h13
      gamma23 := h23
      compact_missed_union := hcompact
      secant_mem := hline2
      secant_ne_source := hlineNe
      gamma3_on_secant := hgamma3On
      secant_core_card := hcoreCases
      source_secant_inter_card_le_two := by
        simpa only [D, D2, line2] using hinterLeTwo
      uncovered_balance := by
        simpa only [H, D, D2, line2] using hHbalance
      core_six_data := by
        simpa only [H, D, D2, line2] using hsix
      core_seven_data := by
        simpa only [H, D, D2, line2] using hseven }⟩

/-- **Three-hole saturation.**  For a source eight-core and a distinct
seven-core meeting it in two coordinates, the uncovered set has size three,
and every selected point off both lines agrees on all three coordinates. -/
theorem uncovered_subset_fullAgreement_of_eight_seven_overlap_two
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 7)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 2)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    (Finset.univ \ (
      jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
        jointCore dom (u 0) (u 1) line2.1 line2.2)).card = 3 ∧
    Finset.univ \ (
      jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
        jointCore dom (u 0) (u 1) line2.1 line2.2) ⊆
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let H := Finset.univ \ (D1 ∪ D2)
  have hD1 : D1.card = 8 := by simpa only [D1] using hcore1
  have hD2 : D2.card = 7 := by simpa only [D2] using hcore2
  have hI : (D1 ∩ D2).card = 2 := by simpa only [D1, D2] using hinter
  have hunionInter := Finset.card_union_add_card_inter D1 D2
  have hHcard : H.card = 3 := by
    have hcomplement : H.card = 16 - (D1 ∪ D2).card := by
      simp only [H, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hn]
    omega
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  have hcap1 : (A ∩ D1).card ≤ 3 := by
    have hcap := fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) (k := 4) (by norm_num)
        (family.degree_lt gamma hgamma) hdeg1.1 hdeg1.2 hoff1
    norm_num at hcap
    simpa only [A, D1] using hcap
  have hcap2 : (A ∩ D2).card ≤ 3 := by
    have hcap := fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) (k := 4) (by norm_num)
        (family.degree_lt gamma hgamma) hdeg2.1 hdeg2.2 hoff2
    norm_num at hcap
    simpa only [A, D2] using hcap
  have hAsub : A ⊆ ((A ∩ D1) ∪ (A ∩ D2)) ∪ (A ∩ H) := by
    intro i hi
    by_cases hi1 : i ∈ D1
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hi1⟩))
    by_cases hi2 : i ∈ D2
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hi, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, by simp only [Finset.mem_union, hi1, hi2,
            or_self, not_false_eq_true]⟩⟩)
  have hAupper : A.card ≤
      (A ∩ D1).card + (A ∩ D2).card + (A ∩ H).card := by
    calc
      A.card ≤ (((A ∩ D1) ∪ (A ∩ D2)) ∪ (A ∩ H)).card :=
        Finset.card_le_card hAsub
      _ ≤ ((A ∩ D1) ∪ (A ∩ D2)).card + (A ∩ H).card :=
        Finset.card_union_le _ _
      _ ≤ ((A ∩ D1).card + (A ∩ D2).card) + (A ∩ H).card := by
        gcongr
        exact Finset.card_union_le _ _
  have hAlower : 9 ≤ A.card :=
    hthreshold.trans (family.threshold_le gamma hgamma)
  have hAHupper : (A ∩ H).card ≤ 3 := by
    exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hHcard
  have hAHcard : (A ∩ H).card = 3 := by omega
  have hAHeq : A ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    omega
  refine ⟨by simpa only [H, D1, D2] using hHcard, ?_⟩
  intro i hi
  have : i ∈ A ∩ H := by
    rw [hAHeq]
    simpa only [H, D1, D2] using hi
  exact (Finset.mem_inter.mp this).1

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
#print axioms source_target_core_inter_eq_regularRootTriple_of_overlap_three
#print axioms exists_uniqueCoreCrossTripleResidual_of_card_gt_sixteen
#print axioms uncovered_subset_fullAgreement_of_eight_seven_overlap_two
