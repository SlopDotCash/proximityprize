/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSevenRootSupport
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

/-!
# Rate-quarter `k = 4`: the long stratum over a no-eight seven-core

For two outsiders from a fixed source line, the coordinates left uncovered
by the source core and their secant core are exactly the union of their
canonical missed supports.  The isolation clause in the no-eight residual
therefore strengthens the global-core pair law to

```text
  3 <= |missed gamma union missed beta|.
```

In particular, distinct long outsiders cannot reuse a support of cardinality
at most two.  This is a geometric constraint absent from the abstract
root/support law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial Module Submodule
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The coordinates missed by either of two outsiders are exactly those left
uncovered by the source core and the secant core through the outsiders. -/
theorem uncovered_source_secant_eq_missed_union
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {line : LineParameter F} {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family line)
    (hbeta : beta ∈ outsideLine family line)
    (hne : gamma ≠ beta) :
    uncoveredByTwoLineCores dom (u 0) (u 1) line
        (secantParameter family gamma beta) =
      sourceSevenMissedSet family line gamma ∪
        sourceSevenMissedSet family line beta := by
  let Aγ := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let Aβ := fullAgreement dom (u 0) (u 1) beta (family.q beta)
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let V := sourceComplement family line
  let Sγ := sourceFreshAgreement family line gamma
  let Sβ := sourceFreshAgreement family line beta
  let Eγ := sourceSevenMissedSet family line gamma
  let Eβ := sourceSevenMissedSet family line beta
  have hgammaData :=
    (mem_outsideLine_iff family line gamma).mp hgamma
  have hbetaData :=
    (mem_outsideLine_iff family line beta).mp hbeta
  have hgammaOn : gamma ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgammaData.1
  have hbetaOn : beta ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hbetaData.1 hne
  have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
  have hcoreEq : Aγ ∩ Aβ = D2 := by
    dsimp only [Aγ, Aβ, D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have hfreshEq : Sγ ∩ Sβ = D2 \ D := by
    rw [← hcoreEq]
    ext i
    simp only [Sγ, Sβ, sourceFreshAgreement, Aγ, Aβ, D,
      Finset.mem_inter, Finset.mem_sdiff]
    tauto
  ext i
  have hfreshMem :
      (i ∈ Sγ ∧ i ∈ Sβ) ↔ (i ∈ D2 ∧ i ∉ D) := by
    rw [← Finset.mem_inter, hfreshEq]
    simp only [Finset.mem_sdiff]
  simp only [uncoveredByTwoLineCores, sourceSevenMissedSet,
    sourceComplement, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_union, not_or]
  constructor
  · rintro ⟨hiD, hiD2⟩
    by_cases hiSγ : i ∈ Sγ
    · right
      exact ⟨hiD, fun hiSβ ↦ hiD2 (hfreshMem.mp ⟨hiSγ, hiSβ⟩).1⟩
    · left
      exact ⟨hiD, hiSγ⟩
  · rintro (⟨hiD, hiSγ⟩ | ⟨hiD, hiSβ⟩)
    · refine ⟨hiD, ?_⟩
      intro hiD2
      exact hiSγ (hfreshMem.mpr ⟨hiD2, hiD⟩).1
    · refine ⟨hiD, ?_⟩
      intro hiD2
      exact hiSβ (hfreshMem.mpr ⟨hiD2, hiD⟩).2

/-- No-eight isolation upgrades the pair law: two distinct source outsiders
miss at least three complement coordinates between them. -/
theorem three_le_missed_union_of_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : NoEightCoreIntermediateResidual family)
    {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family residual.source)
    (hbeta : beta ∈ outsideLine family residual.source)
    (hne : gamma ≠ beta) :
    3 ≤
      ((sourceSevenMissedSet family residual.source gamma) ∪
        (sourceSevenMissedSet family residual.source beta)).card := by
  let line2 := secantParameter family gamma beta
  have hgammaData :=
    (mem_outsideLine_iff family residual.source gamma).mp hgamma
  have hbetaData :=
    (mem_outsideLine_iff family residual.source beta).mp hbeta
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.1 hbetaData.1 hne
  have hisolated := residual.three_le_uncovered line2 hline2
  rw [uncovered_source_secant_eq_missed_union
    family hgamma hbeta hne] at hisolated
  exact hisolated

/-- Canonical missed supports of distinct long outsiders are unequal. -/
theorem sourceSevenMissedSet_ne_of_long_outsiders
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : NoEightCoreIntermediateResidual family)
    {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family residual.source)
    (hbeta : beta ∈ outsideLine family residual.source)
    (hgammaLong :
      (sourceSevenMissedSet family residual.source gamma).card ≤ 2)
    (hbetaLong :
      (sourceSevenMissedSet family residual.source beta).card ≤ 2)
    (hne : gamma ≠ beta) :
    sourceSevenMissedSet family residual.source gamma ≠
      sourceSevenMissedSet family residual.source beta := by
  intro heq
  have hthree := three_le_missed_union_of_noEight_source_seven
    family residual hgamma hbeta hne
  rw [heq, Finset.union_self] at hthree
  have hgammaSmall :
      (sourceSevenMissedSet family residual.source beta).card ≤ 2 := by
    simpa only [heq] using hgammaLong
  have htwice := Nat.add_le_add hgammaSmall hbetaLong
  omega

/-! ## All-outsider ternary coupling -/

/-- **All-outsider root/missed balance.**  Three arbitrary outsiders from a
size-seven source are collinear whenever their common source-root block and
their common fresh block contain at least four coordinates in total.  In
subtraction-free form, the hypothesis is

`4 + |E1 ∪ E2 ∪ E3| ≤ 9 + |T1 ∩ T2 ∩ T3|`.

Unlike the regular-stratum version, no root or missed-support cardinality is
assumed. -/
theorem third_outside_mem_pointsOn_secant_of_root_missed_balance
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ outsideLine family line)
    (hgamma2 : gamma2 ∈ outsideLine family line)
    (hgamma3 : gamma3 ∈ outsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hbalance :
      4 + (((sourceSevenMissedSet family line gamma1 ∪
          sourceSevenMissedSet family line gamma2) ∪
        sourceSevenMissedSet family line gamma3).card) ≤
      9 + ((((overlapRootBlock dom (u 0) (u 1) gamma1
          (family.q gamma1) line) ∩
        overlapRootBlock dom (u 0) (u 1) gamma2
          (family.q gamma2) line) ∩
        overlapRootBlock dom (u 0) (u 1) gamma3
          (family.q gamma3) line).card)) :
    gamma3 ∈ pointsOn family (secantParameter family gamma1 gamma2) := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let T1 := overlapRootBlock dom (u 0) (u 1) gamma1
    (family.q gamma1) line
  let T2 := overlapRootBlock dom (u 0) (u 1) gamma2
    (family.q gamma2) line
  let T3 := overlapRootBlock dom (u 0) (u 1) gamma3
    (family.q gamma3) line
  let E1 := sourceSevenMissedSet family line gamma1
  let E2 := sourceSevenMissedSet family line gamma2
  let E3 := sourceSevenMissedSet family line gamma3
  let C0 := (T1 ∩ T2) ∩ T3
  let H := V \ ((E1 ∪ E2) ∪ E3)
  let R := C0 ∪ H
  let A : F → Finset I := fun gamma ↦
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  have hVcard : V.card = 9 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsource]
  have hEsub : (E1 ∪ E2) ∪ E3 ⊆ V := by
    apply Finset.union_subset
    · apply Finset.union_subset <;> intro i hi
      · exact (Finset.mem_sdiff.mp hi).1
      · exact (Finset.mem_sdiff.mp hi).1
    · intro i hi
      exact (Finset.mem_sdiff.mp hi).1
  have hHbook : H.card + ((E1 ∪ E2) ∪ E3).card = 9 := by
    have hsplit := Finset.card_sdiff_add_card_inter V ((E1 ∪ E2) ∪ E3)
    have hinter : V ∩ ((E1 ∪ E2) ∪ E3) = (E1 ∪ E2) ∪ E3 :=
      Finset.inter_eq_right.mpr hEsub
    rw [hinter, hVcard] at hsplit
    simpa only [H] using hsplit
  have hCsubD : C0 ⊆ D := by
    intro i hi
    have hiT1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1
    exact (Finset.mem_inter.mp (by
      simpa only [T1, overlapRootBlock, D] using hiT1)).2
  have hHsubV : H ⊆ V := Finset.sdiff_subset
  have hCHdis : Disjoint C0 H := by
    rw [Finset.disjoint_left]
    intro i hiC hiH
    have hiD := hCsubD hiC
    have hiV := hHsubV hiH
    exact (Finset.mem_sdiff.mp hiV).2 hiD
  have hRcard : 4 ≤ R.card := by
    have hcard := Finset.card_union_of_disjoint hCHdis
    change R.card = C0.card + H.card at hcard
    change 4 + ((E1 ∪ E2) ∪ E3).card ≤ 9 + C0.card at hbalance
    omega
  have hRsub : R ⊆ (A gamma1 ∩ A gamma2) ∩ A gamma3 := by
    intro i hi
    rcases Finset.mem_union.mp (by simpa only [R] using hi) with hiC | hiH
    · have hiCData := Finset.mem_inter.mp hiC
      have hi12 := Finset.mem_inter.mp hiCData.1
      have hi1 : i ∈ A gamma1 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T1, overlapRootBlock] using hi12.1)).1
      have hi2 : i ∈ A gamma2 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T2, overlapRootBlock] using hi12.2)).1
      have hi3 : i ∈ A gamma3 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T3, overlapRootBlock] using hiCData.2)).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hi1, hi2⟩, hi3⟩
    · have hiData := Finset.mem_sdiff.mp (by simpa only [H] using hiH)
      have hiV := hiData.1
      have hiNot := hiData.2
      have fresh_of_not_missed (gamma : F) (E : Finset I)
          (hE : E = sourceSevenMissedSet family line gamma)
          (hiE : i ∉ E) : i ∈ sourceFreshAgreement family line gamma := by
        by_contra hiFresh
        apply hiE
        rw [hE]
        exact Finset.mem_sdiff.mpr ⟨hiV, hiFresh⟩
      have hi1Fresh := fresh_of_not_missed gamma1 E1 rfl
        (fun hiE1 ↦ hiNot (by simp [hiE1]))
      have hi2Fresh := fresh_of_not_missed gamma2 E2 rfl
        (fun hiE2 ↦ hiNot (by simp [hiE2]))
      have hi3Fresh := fresh_of_not_missed gamma3 E3 rfl
        (fun hiE3 ↦ hiNot (by simp [hiE3]))
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi1Fresh).1,
          (Finset.mem_sdiff.mp hi2Fresh).1⟩,
        (Finset.mem_sdiff.mp hi3Fresh).1⟩
  have htriple : 3 < ((A gamma1 ∩ A gamma2) ∩ A gamma3).card := by
    have hRlarge : 3 < R.card := by omega
    exact hRlarge.trans_le (Finset.card_le_card hRsub)
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp hgamma1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp hgamma2 |>.1
  have hgamma3G := (mem_outsideLine_iff family line gamma3).mp hgamma3 |>.1
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

/-! ## Five balanced outsiders contradict the no-eight cap -/

/-- **Terminal geometric consumer.**  Two outsiders and three further
pairwise-distinct outsiders satisfying the ternary root/missed balance all
lie on the first secant.  Five points force that secant core to have size at
least eight, contradicting the no-eight global core cap. -/
theorem false_of_five_outsiders_root_missed_balance
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma1 gamma2 gamma3 gamma4 gamma5 : F}
    (hgamma1 : gamma1 ∈ outsideLine family residual.source)
    (hgamma2 : gamma2 ∈ outsideLine family residual.source)
    (hgamma3 : gamma3 ∈ outsideLine family residual.source)
    (hgamma4 : gamma4 ∈ outsideLine family residual.source)
    (hgamma5 : gamma5 ∈ outsideLine family residual.source)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (h14 : gamma1 ≠ gamma4) (h15 : gamma1 ≠ gamma5)
    (h23 : gamma2 ≠ gamma3) (h24 : gamma2 ≠ gamma4)
    (h25 : gamma2 ≠ gamma5) (h34 : gamma3 ≠ gamma4)
    (h35 : gamma3 ≠ gamma5) (h45 : gamma4 ≠ gamma5)
    (hbalance3 :
      4 + (((sourceSevenMissedSet family residual.source gamma1 ∪
          sourceSevenMissedSet family residual.source gamma2) ∪
        sourceSevenMissedSet family residual.source gamma3).card) ≤
      9 + ((((overlapRootBlock dom (u 0) (u 1) gamma1
          (family.q gamma1) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma2
          (family.q gamma2) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma3
          (family.q gamma3) residual.source).card))
    (hbalance4 :
      4 + (((sourceSevenMissedSet family residual.source gamma1 ∪
          sourceSevenMissedSet family residual.source gamma2) ∪
        sourceSevenMissedSet family residual.source gamma4).card) ≤
      9 + ((((overlapRootBlock dom (u 0) (u 1) gamma1
          (family.q gamma1) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma2
          (family.q gamma2) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma4
          (family.q gamma4) residual.source).card))
    (hbalance5 :
      4 + (((sourceSevenMissedSet family residual.source gamma1 ∪
          sourceSevenMissedSet family residual.source gamma2) ∪
        sourceSevenMissedSet family residual.source gamma5).card) ≤
      9 + ((((overlapRootBlock dom (u 0) (u 1) gamma1
          (family.q gamma1) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma2
          (family.q gamma2) residual.source) ∩
        overlapRootBlock dom (u 0) (u 1) gamma5
          (family.q gamma5) residual.source).card)) :
    False := by
  let line2 := secantParameter family gamma1 gamma2
  let G5 : Finset F := {gamma1, gamma2, gamma3, gamma4, gamma5}
  have hgamma1Data :=
    (mem_outsideLine_iff family residual.source gamma1).mp hgamma1
  have hgamma2Data :=
    (mem_outsideLine_iff family residual.source gamma2).mp hgamma2
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgamma1Data.1 hgamma2Data.1 h12
  have hgamma1On : gamma1 ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgamma1Data.1
  have hgamma2On : gamma2 ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hgamma2Data.1 h12
  have hgamma3On : gamma3 ∈ pointsOn family line2 := by
    simpa only [line2] using
      third_outside_mem_pointsOn_secant_of_root_missed_balance
        family hn hsource hgamma1 hgamma2 hgamma3 h12 h13 hbalance3
  have hgamma4On : gamma4 ∈ pointsOn family line2 := by
    simpa only [line2] using
      third_outside_mem_pointsOn_secant_of_root_missed_balance
        family hn hsource hgamma1 hgamma2 hgamma4 h12 h14 hbalance4
  have hgamma5On : gamma5 ∈ pointsOn family line2 := by
    simpa only [line2] using
      third_outside_mem_pointsOn_secant_of_root_missed_balance
        family hn hsource hgamma1 hgamma2 hgamma5 h12 h15 hbalance5
  have h1not : gamma1 ∉ ({gamma2, gamma3, gamma4, gamma5} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13, h14, h15⟩
  have h2not : gamma2 ∉ ({gamma3, gamma4, gamma5} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h23, h24, h25⟩
  have h3not : gamma3 ∉ ({gamma4, gamma5} : Finset F) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h34, h35⟩
  have h4not : gamma4 ∉ ({gamma5} : Finset F) := by
    simpa only [Finset.mem_singleton] using h45
  have hG5card : G5.card = 5 := by
    change ((insert gamma1 (insert gamma2
      (insert gamma3
        (insert gamma4 ({gamma5} : Finset F)))) : Finset F)).card = 5
    rw [Finset.card_insert_of_notMem h1not,
      Finset.card_insert_of_notMem h2not,
      Finset.card_insert_of_notMem h3not,
      Finset.card_insert_of_notMem h4not]
    simp only [Finset.card_singleton]
  have hG5sub : G5 ⊆ pointsOn family line2 := by
    intro gamma hgamma
    simp only [G5, Finset.mem_insert, Finset.mem_singleton] at hgamma
    rcases hgamma with rfl | rfl | rfl | rfl | rfl
    · exact hgamma1On
    · exact hgamma2On
    · exact hgamma3On
    · exact hgamma4On
    · exact hgamma5On
  have hpoints : 5 ≤ (pointsOn family line2).card := by
    rw [← hG5card]
    exact Finset.card_le_card hG5sub
  have hcoreLower : 8 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card :=
    eight_le_core_of_five_le_pointsOn
      family hn hthreshold hline2 hpoints
  have hcoreUpper :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 7 :=
    residual.global_core_cap line2 hline2
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenLongStratum
#print axioms uncovered_source_secant_eq_missed_union
#print axioms three_le_missed_union_of_noEight_source_seven
#print axioms sourceSevenMissedSet_ne_of_long_outsiders
#print axioms third_outside_mem_pointsOn_secant_of_root_missed_balance
#print axioms false_of_five_outsiders_root_missed_balance
