/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSevenRootSupport

/-!
# Rate-quarter `k = 4`: fixed-root rigidity for a no-eight seven-core

For a size-seven source core, a regular outsider has six fresh agreements,
three source-core roots, and a three-coordinate missed set in the
nine-coordinate source complement.  The global core-seven cap implies that
two regular outsiders with the same root triple have missed sets meeting in
at most one coordinate.

The degree-three coupling rules out the twelve-point affine-plane fibers from
the abstract signature countermodel.  A coordinate fresh for three outsiders
is a fourth common root after adjoining their common source-root triple, so
the three polynomial points are collinear.  Among four missed triples with
pair intersections at most one, either two relevant triple unions leave such
fresh coordinates, or three missed triples partition the complement; in the
partition case the fourth triple supplies the fresh coordinates after
rebasing the secant.  Thus all four polynomial points would be collinear.

Four selected points on one relevant line force its core to have size seven.
Three of their six-point fresh sets would then have one common four-point
pair intersection.  Removing that common part gives three disjoint two-sets
inside a five-set, which is impossible.  Hence every fixed source-root triple
carries at most three regular outsiders.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootFiber

attribute [local instance] Classical.propDecidable

/-! ## Finite-set obstructions -/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Three six-subsets of a nine-set cannot have all three pairwise
intersections equal to one common four-set. -/
theorem no_three_six_sets_with_common_four_intersection
    (V P S1 S2 S3 : Finset U)
    (hVcard : V.card = 9) (hPcard : P.card = 4)
    (hS1sub : S1 ⊆ V) (hS2sub : S2 ⊆ V) (hS3sub : S3 ⊆ V)
    (hS1card : S1.card = 6) (hS2card : S2.card = 6)
    (hS3card : S3.card = 6)
    (h12 : S1 ∩ S2 = P) (h13 : S1 ∩ S3 = P)
    (h23 : S2 ∩ S3 = P) : False := by
  have hPsub1 : P ⊆ S1 := by
    rw [← h12]
    exact Finset.inter_subset_left
  have hPsub2 : P ⊆ S2 := by
    rw [← h12]
    exact Finset.inter_subset_right
  have hPsub3 : P ⊆ S3 := by
    rw [← h13]
    exact Finset.inter_subset_right
  have hPsubV : P ⊆ V := hPsub1.trans hS1sub
  let R1 := S1 \ P
  let R2 := S2 \ P
  let R3 := S3 \ P
  have hR1card : R1.card = 2 := by
    simp only [R1, Finset.card_sdiff_of_subset hPsub1, hS1card, hPcard]
  have hR2card : R2.card = 2 := by
    simp only [R2, Finset.card_sdiff_of_subset hPsub2, hS2card, hPcard]
  have hR3card : R3.card = 2 := by
    simp only [R3, Finset.card_sdiff_of_subset hPsub3, hS3card, hPcard]
  have hR1sub : R1 ⊆ V \ P := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hS1sub (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hR2sub : R2 ⊆ V \ P := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hS2sub (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hR3sub : R3 ⊆ V \ P := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hS3sub (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hR12 : Disjoint R1 R2 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hiP : i ∈ P := by
      rw [← h12]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi1).1, (Finset.mem_sdiff.mp hi2).1⟩
    exact (Finset.mem_sdiff.mp hi1).2 hiP
  have hR13 : Disjoint R1 R3 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi3
    have hiP : i ∈ P := by
      rw [← h13]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi1).1, (Finset.mem_sdiff.mp hi3).1⟩
    exact (Finset.mem_sdiff.mp hi1).2 hiP
  have hR23 : Disjoint R2 R3 := by
    rw [Finset.disjoint_left]
    intro i hi2 hi3
    have hiP : i ∈ P := by
      rw [← h23]
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi2).1, (Finset.mem_sdiff.mp hi3).1⟩
    exact (Finset.mem_sdiff.mp hi2).2 hiP
  have hUnionSub : (R1 ∪ R2) ∪ R3 ⊆ V \ P :=
    Finset.union_subset (Finset.union_subset hR1sub hR2sub) hR3sub
  have hR12Union : (R1 ∪ R2).card = 4 := by
    rw [Finset.card_union_of_disjoint hR12, hR1card, hR2card]
  have hR123 : ((R1 ∪ R2) ∪ R3).card = 6 := by
    have hdis : Disjoint (R1 ∪ R2) R3 :=
      Finset.disjoint_union_left.mpr ⟨hR13, hR23⟩
    rw [Finset.card_union_of_disjoint hdis, hR12Union, hR3card]
  have hVdiff : (V \ P).card = 5 := by
    rw [Finset.card_sdiff_of_subset hPsubV, hVcard, hPcard]
  have hle := Finset.card_le_card hUnionSub
  rw [hR123, hVdiff] at hle
  omega

/-- If three three-subsets partition a nine-set, adjoining a fourth
three-subset that meets the omitted partition block in at most one point
gives union size at most seven. -/
theorem partition_pair_union_fourth_card_le_seven
    (V E1 E2 E3 E4 : Finset U)
    (hVcard : V.card = 9)
    (hE1card : E1.card = 3) (hE2card : E2.card = 3)
    (hE3card : E3.card = 3) (hE4card : E4.card = 3)
    (hE4sub : E4 ⊆ V)
    (hpartition : (E1 ∪ E2) ∪ E3 = V)
    (hinter43 : (E4 ∩ E3).card ≤ 1) :
    ((E1 ∪ E2) ∪ E4).card ≤ 7 := by
  let W := E1 ∪ E2
  have hWbook := Finset.card_union_add_card_inter E1 E2
  have hpartitionCard : (W ∪ E3).card = 9 := by
    rw [show W ∪ E3 = V by simpa only [W] using hpartition, hVcard]
  have htotalBook := Finset.card_union_add_card_inter W E3
  have hWle : W.card ≤ 6 := by
    exact (Finset.card_union_le E1 E2).trans_eq (by omega)
  have hWcard : W.card = 6 := by
    omega
  have hWE3dis : Disjoint W E3 := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    omega
  have hE4cover : E4 ⊆ W ∪ E3 := by
    intro i hi
    rw [show W ∪ E3 = V by simpa only [W] using hpartition]
    exact hE4sub hi
  have hE4split : E4 = (E4 ∩ W) ∪ (E4 ∩ E3) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp (hE4cover hi) with hiW | hi3
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hiW⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi3⟩)
    · intro hi
      rcases Finset.mem_union.mp hi with hiW | hi3
      · exact (Finset.mem_inter.mp hiW).1
      · exact (Finset.mem_inter.mp hi3).1
  have hsplitDis : Disjoint (E4 ∩ W) (E4 ∩ E3) := by
    exact (hWE3dis.mono Finset.inter_subset_right
      Finset.inter_subset_right)
  have hsplitCard := congrArg Finset.card hE4split
  rw [Finset.card_union_of_disjoint hsplitDis, hE4card] at hsplitCard
  have hinterW : 2 ≤ (W ∩ E4).card := by
    rw [Finset.inter_comm]
    omega
  have hunionBook := Finset.card_union_add_card_inter W E4
  change (W ∪ E4).card ≤ 7
  omega

/-! ## Seven-core regular signatures -/

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A regular outsider from a size-seven source misses exactly three of the
nine source-complement coordinates. -/
theorem regularMissedEdge_card_eq_three_of_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    (regularMissedEdge family line gamma).card = 3 := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let S := sourceFreshAgreement family line gamma
  have hgammaData := hgamma
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
  have hVcard : V.card = 9 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsource]
  have hSsub : S ⊆ V := by
    simpa only [S, V, D] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  change (V \ S).card = 3
  rw [Finset.card_sdiff_of_subset hSsub, hVcard, hgammaData.2.1]

/-- In the nine-coordinate source complement, two regular fresh six-sets
meet in `3 + |E_gamma ∩ E_beta|` coordinates. -/
theorem regular_fresh_inter_card_eq_three_add_missed_inter_of_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line) :
    (sourceFreshAgreement family line gamma ∩
        sourceFreshAgreement family line beta).card =
      3 + (regularMissedEdge family line gamma ∩
        regularMissedEdge family line beta).card := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let Sg := sourceFreshAgreement family line gamma
  let Sb := sourceFreshAgreement family line beta
  let Eg := regularMissedEdge family line gamma
  let Eb := regularMissedEdge family line beta
  have hVcard : V.card = 9 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsource]
  have hSgsub : Sg ⊆ V := by
    simpa only [Sg, V, D] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hSbsub : Sb ⊆ V := by
    simpa only [Sb, V, D] using
      sourceFreshAgreement_subset_coreComplement family line beta
  have hEg : Eg = V \ Sg := rfl
  have hEb : Eb = V \ Sb := rfl
  have hSg : Sg = V \ Eg := by
    rw [hEg]
    ext i
    simp only [Finset.mem_sdiff]
    tauto
  have hSb : Sb = V \ Eb := by
    rw [hEb]
    ext i
    simp only [Finset.mem_sdiff]
    tauto
  have hEgcard : Eg.card = 3 := by
    simpa only [Eg] using
      regularMissedEdge_card_eq_three_of_source_seven
        family hn hsource hgamma
  have hEbcard : Eb.card = 3 := by
    simpa only [Eb] using
      regularMissedEdge_card_eq_three_of_source_seven
        family hn hsource hbeta
  have hEunionSub : Eg ∪ Eb ⊆ V := by
    rw [hEg, hEb]
    exact Finset.union_subset Finset.sdiff_subset Finset.sdiff_subset
  have hfreshEq : Sg ∩ Sb = V \ (Eg ∪ Eb) := by
    rw [hSg, hSb]
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hpartition := Finset.card_sdiff_add_card_inter V (Eg ∪ Eb)
  have hinter : V ∩ (Eg ∪ Eb) = Eg ∪ Eb :=
    Finset.inter_eq_right.mpr hEunionSub
  have hunion := Finset.card_union_add_card_inter Eg Eb
  change (Sg ∩ Sb).card = 3 + (Eg ∩ Eb).card
  rw [hfreshEq]
  rw [hinter] at hpartition
  omega

/-- The global core-seven cap becomes the exact pair inequality
`|T_gamma ∩ T_beta| + |E_gamma ∩ E_beta| <= 4`. -/
theorem root_inter_add_missed_inter_le_four_of_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family residual.source)
    (hbeta : beta ∈ regularOutsideLine family residual.source)
    (hne : gamma ≠ beta) :
    (regularRootTriple family residual.source gamma ∩
        regularRootTriple family residual.source beta).card +
      (regularMissedEdge family residual.source gamma ∩
        regularMissedEdge family residual.source beta).card ≤ 4 := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let Tg := regularRootTriple family residual.source gamma
  let Tb := regularRootTriple family residual.source beta
  let Sg := sourceFreshAgreement family residual.source gamma
  let Sb := sourceFreshAgreement family residual.source beta
  have hgammaData := hgamma
  have hbetaData := hbeta
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData hbetaData
  have hgammaOut :=
    (mem_outsideLine_iff family residual.source gamma).mp hgammaData.1
  have hbetaOut :=
    (mem_outsideLine_iff family residual.source beta).mp hbetaData.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaOut.1 hbetaOut.1 hne
  have hgammaOn : gamma ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgammaOut.1
  have hbetaOn : beta ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hbetaOut.1 hne
  have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) = D2 := by
    dsimp only [D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have hD2cap : D2.card ≤ 7 := by
    simpa only [D2] using residual.global_core_cap line2 hline2
  have hrootEq : Tg ∩ Tb = D2 ∩ D := by
    rw [← hcoreEq]
    ext i
    simp only [Tg, Tb, regularRootTriple, D, Finset.mem_inter]
    tauto
  have hfreshEq : Sg ∩ Sb = D2 \ D := by
    rw [← hcoreEq]
    ext i
    simp only [Sg, Sb, sourceFreshAgreement, D,
      Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  have hfreshCard :=
    regular_fresh_inter_card_eq_three_add_missed_inter_of_source_seven
      family hn hsource hgamma hbeta
  change (Tg ∩ Tb).card +
      (regularMissedEdge family residual.source gamma ∩
        regularMissedEdge family residual.source beta).card ≤ 4
  rw [hfreshEq] at hfreshCard
  rw [hrootEq]
  have hsplit' : (D2 \ D).card + (D ∩ D2).card = D2.card := by
    simpa only [Finset.inter_comm D D2] using hsplit
  omega

/-- Equal-root regular outsiders from a no-eight seven-core have missed
triples meeting in at most one coordinate. -/
theorem missed_inter_card_le_one_of_noEight_source_seven_same_root
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family residual.source)
    (hbeta : beta ∈ regularOutsideLine family residual.source)
    (hne : gamma ≠ beta)
    (hroot : regularRootTriple family residual.source gamma =
      regularRootTriple family residual.source beta) :
    (regularMissedEdge family residual.source gamma ∩
      regularMissedEdge family residual.source beta).card ≤ 1 := by
  have hsum :=
    root_inter_add_missed_inter_le_four_of_noEight_source_seven
      family hn residual hsource hgamma hbeta hne
  have hrootCard :
      (regularRootTriple family residual.source gamma).card = 3 := by
    have hgammaData := hgamma
    simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
    simpa only [regularRootTriple] using hgammaData.2.2.2
  have hinterRoot :
      (regularRootTriple family residual.source gamma ∩
        regularRootTriple family residual.source beta).card = 3 := by
    rw [← hroot, Finset.inter_self, hrootCard]
  omega

/-! ## A common fresh coordinate forces cubic collinearity -/

/-- Three regular outsiders with one source-root triple are collinear as soon
as they share one fresh coordinate.  The root triple and that coordinate give
four common full-agreement roots, exceeding the degree-three noncollinear
cap. -/
theorem third_regular_mem_pointsOn_secant_of_same_root_of_common_fresh
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {line : LineParameter F}
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2)
    (hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3)
    {i : I}
    (hi1 : i ∈ sourceFreshAgreement family line gamma1)
    (hi2 : i ∈ sourceFreshAgreement family line gamma2)
    (hi3 : i ∈ sourceFreshAgreement family line gamma3) :
    gamma3 ∈ pointsOn family (secantParameter family gamma1 gamma2) := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let T := regularRootTriple family line gamma1
  let R := insert i T
  let A : F → Finset I := fun gamma ↦
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  have hTcard : T.card = 3 := by
    simpa only [T, regularRootTriple] using hgamma1Data.2.2.2
  have hiNotT : i ∉ T := by
    intro hiT
    have hiD : i ∈ D := by
      exact (Finset.mem_inter.mp (by
        simpa only [T, regularRootTriple, D] using hiT)).2
    exact (Finset.mem_sdiff.mp hi1).2 hiD
  have hRcard : R.card = 4 := by
    rw [show R = insert i T by rfl, Finset.card_insert_of_notMem hiNotT,
      hTcard]
  have hRsub : R ⊆ (A gamma1 ∩ A gamma2) ∩ A gamma3 := by
    intro j hj
    rcases Finset.mem_insert.mp (by simpa only [R] using hj) with rfl | hjT
    · exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hi1).1, (Finset.mem_sdiff.mp hi2).1⟩,
          (Finset.mem_sdiff.mp hi3).1⟩
    · have hj1 : j ∈ A gamma1 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T, regularRootTriple] using hjT)).1
      have hj2Root : j ∈ regularRootTriple family line gamma2 := by
        rw [← hroot12]
        simpa only [T] using hjT
      have hj3Root : j ∈ regularRootTriple family line gamma3 := by
        rw [← hroot13]
        simpa only [T] using hjT
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨hj1, (Finset.mem_inter.mp (by
          simpa only [regularRootTriple] using hj2Root)).1⟩,
        (Finset.mem_inter.mp (by
          simpa only [regularRootTriple] using hj3Root)).1⟩
  have htriple : 3 < ((A gamma1 ∩ A gamma2) ∩ A gamma3).card := by
    have hRlarge : 3 < R.card := by omega
    exact hRlarge.trans_le (Finset.card_le_card hRsub)
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

/-- Cardinal form: if three same-root missed triples cover at most eight of
the nine complement coordinates, their complementary fresh sets share an
anchor and the three polynomial points are collinear. -/
theorem third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2)
    (hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3)
    (hunion :
      ((regularMissedEdge family line gamma1 ∪
          regularMissedEdge family line gamma2) ∪
        regularMissedEdge family line gamma3).card ≤ 8) :
    gamma3 ∈ pointsOn family (secantParameter family gamma1 gamma2) := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
  let R := V \ ((E1 ∪ E2) ∪ E3)
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
  have hRcard : 1 ≤ R.card := by
    have hsplit := Finset.card_sdiff_add_card_inter V ((E1 ∪ E2) ∪ E3)
    have hinter : V ∩ ((E1 ∪ E2) ∪ E3) = (E1 ∪ E2) ∪ E3 :=
      Finset.inter_eq_right.mpr hEsub
    rw [hinter, hVcard] at hsplit
    change R.card + ((E1 ∪ E2) ∪ E3).card = 9 at hsplit
    change ((E1 ∪ E2) ∪ E3).card ≤ 8 at hunion
    omega
  obtain ⟨i, hiR⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  have hiData := Finset.mem_sdiff.mp hiR
  have hiV := hiData.1
  have hiNot := hiData.2
  have fresh_of_not_missed (gamma : F) (E : Finset I)
      (hE : E = regularMissedEdge family line gamma) (hiE : i ∉ E) :
      i ∈ sourceFreshAgreement family line gamma := by
    by_contra hiFresh
    apply hiE
    rw [hE]
    exact Finset.mem_sdiff.mpr ⟨hiV, hiFresh⟩
  have hi1 : i ∈ sourceFreshAgreement family line gamma1 :=
    fresh_of_not_missed gamma1 E1 rfl
      (fun hiE1 ↦ hiNot (by simp [hiE1]))
  have hi2 : i ∈ sourceFreshAgreement family line gamma2 :=
    fresh_of_not_missed gamma2 E2 rfl
      (fun hiE2 ↦ hiNot (by simp [hiE2]))
  have hi3 : i ∈ sourceFreshAgreement family line gamma3 :=
    fresh_of_not_missed gamma3 E3 rfl
      (fun hiE3 ↦ hiNot (by simp [hiE3]))
  exact third_regular_mem_pointsOn_secant_of_same_root_of_common_fresh
    family hgamma1 hgamma2 hgamma3 h12 h13 hroot12 hroot13 hi1 hi2 hi3

/-- **Cross-root locator criterion.**  Three regular outsiders are collinear
whenever their common source-root block and their common fresh block contain
at least four coordinates in total.  The displayed subtraction-free
hypothesis is exactly

`4 <= |T1 ∩ T2 ∩ T3| + (9 - |E1 ∪ E2 ∪ E3|)`.

This is the ternary polynomial constraint absent from the abstract pairwise
signature countermodel. -/
theorem third_regular_mem_pointsOn_secant_of_root_missed_balance
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (hbalance :
      4 + (((regularMissedEdge family line gamma1 ∪
          regularMissedEdge family line gamma2) ∪
        regularMissedEdge family line gamma3).card) ≤
      9 + (((regularRootTriple family line gamma1 ∩
          regularRootTriple family line gamma2) ∩
        regularRootTriple family line gamma3).card)) :
    gamma3 ∈ pointsOn family (secantParameter family gamma1 gamma2) := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let T1 := regularRootTriple family line gamma1
  let T2 := regularRootTriple family line gamma2
  let T3 := regularRootTriple family line gamma3
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
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
      simpa only [T1, regularRootTriple, D] using hiT1)).2
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
          simpa only [T1, regularRootTriple] using hi12.1)).1
      have hi2 : i ∈ A gamma2 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T2, regularRootTriple] using hi12.2)).1
      have hi3 : i ∈ A gamma3 := by
        exact (Finset.mem_inter.mp (by
          simpa only [T3, regularRootTriple] using hiCData.2)).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hi1, hi2⟩, hi3⟩
    · have hiData := Finset.mem_sdiff.mp (by simpa only [H] using hiH)
      have hiV := hiData.1
      have hiNot := hiData.2
      have fresh_of_not_missed (gamma : F) (E : Finset I)
          (hE : E = regularMissedEdge family line gamma)
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
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp hgamma1Data.1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp hgamma2Data.1 |>.1
  have hgamma3G := (mem_outsideLine_iff family line gamma3).mp hgamma3Data.1 |>.1
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

/-! ## Four equal-root regular outsiders are collinear -/

/-- Four regular outsiders carrying one source-root triple must all lie on
one relevant decoded line.  If the first two missed triples and either of the
other triples do not cover the complement, common fresh anchors put both
remaining points on the first secant.  If three missed triples partition the
complement, rebasing through the fourth point gives the two required anchors. -/
theorem exists_line_of_four_regular_same_root_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma1 gamma2 gamma3 gamma4 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family residual.source)
    (hgamma2 : gamma2 ∈ regularOutsideLine family residual.source)
    (hgamma3 : gamma3 ∈ regularOutsideLine family residual.source)
    (hgamma4 : gamma4 ∈ regularOutsideLine family residual.source)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (h14 : gamma1 ≠ gamma4) (h23 : gamma2 ≠ gamma3)
    (h24 : gamma2 ≠ gamma4) (h34 : gamma3 ≠ gamma4)
    (hroot12 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma2)
    (hroot13 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma3)
    (hroot14 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma4) :
    ∃ line2 : LineParameter F, line2 ∈ lineParameters family ∧
      gamma1 ∈ pointsOn family line2 ∧
      gamma2 ∈ pointsOn family line2 ∧
      gamma3 ∈ pointsOn family line2 ∧
      gamma4 ∈ pointsOn family line2 := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let V : Finset I := Finset.univ \ D
  let E1 := regularMissedEdge family residual.source gamma1
  let E2 := regularMissedEdge family residual.source gamma2
  let E3 := regularMissedEdge family residual.source gamma3
  let E4 := regularMissedEdge family residual.source gamma4
  have hVcard : V.card = 9 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsource]
  have hE1card : E1.card = 3 := by
    simpa only [E1] using regularMissedEdge_card_eq_three_of_source_seven
      family hn hsource hgamma1
  have hE2card : E2.card = 3 := by
    simpa only [E2] using regularMissedEdge_card_eq_three_of_source_seven
      family hn hsource hgamma2
  have hE3card : E3.card = 3 := by
    simpa only [E3] using regularMissedEdge_card_eq_three_of_source_seven
      family hn hsource hgamma3
  have hE4card : E4.card = 3 := by
    simpa only [E4] using regularMissedEdge_card_eq_three_of_source_seven
      family hn hsource hgamma4
  have hE1sub : E1 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hE2sub : E2 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hE3sub : E3 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hE4sub : E4 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hroot23 : regularRootTriple family residual.source gamma2 =
      regularRootTriple family residual.source gamma3 :=
    hroot12.symm.trans hroot13
  have hroot24 : regularRootTriple family residual.source gamma2 =
      regularRootTriple family residual.source gamma4 :=
    hroot12.symm.trans hroot14
  have hroot34 : regularRootTriple family residual.source gamma3 =
      regularRootTriple family residual.source gamma4 :=
    hroot13.symm.trans hroot14
  have hinter12 : (E1 ∩ E2).card ≤ 1 := by
    simpa only [E1, E2] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma1 hgamma2 h12 hroot12
  have hinter13 : (E1 ∩ E3).card ≤ 1 := by
    simpa only [E1, E3] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma1 hgamma3 h13 hroot13
  have hinter14 : (E1 ∩ E4).card ≤ 1 := by
    simpa only [E1, E4] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma1 hgamma4 h14 hroot14
  have hinter23 : (E2 ∩ E3).card ≤ 1 := by
    simpa only [E2, E3] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma2 hgamma3 h23 hroot23
  have hinter24 : (E2 ∩ E4).card ≤ 1 := by
    simpa only [E2, E4] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma2 hgamma4 h24 hroot24
  have hinter34 : (E3 ∩ E4).card ≤ 1 := by
    simpa only [E3, E4] using
      missed_inter_card_le_one_of_noEight_source_seven_same_root
        family hn residual hsource hgamma3 hgamma4 h34 hroot34
  have union_card_le_eight_of_ne
      (A B C : Finset I) (hsub : (A ∪ B) ∪ C ⊆ V)
      (hne : (A ∪ B) ∪ C ≠ V) : ((A ∪ B) ∪ C).card ≤ 8 := by
    have hle := Finset.card_le_card hsub
    rw [hVcard] at hle
    by_contra hnot
    have heq : (A ∪ B) ∪ C = V := by
      apply Finset.eq_of_subset_of_card_le hsub
      omega
    exact hne heq
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  have hgamma4Data := hgamma4
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma4Data
  have hgamma1G :=
    (mem_outsideLine_iff family residual.source gamma1).mp hgamma1Data.1 |>.1
  have hgamma2G :=
    (mem_outsideLine_iff family residual.source gamma2).mp hgamma2Data.1 |>.1
  have hgamma3G :=
    (mem_outsideLine_iff family residual.source gamma3).mp hgamma3Data.1 |>.1
  have hgamma4G :=
    (mem_outsideLine_iff family residual.source gamma4).mp hgamma4Data.1 |>.1
  by_cases h123 : (E1 ∪ E2) ∪ E3 = V
  · have h124card : ((E1 ∪ E2) ∪ E4).card ≤ 7 :=
      partition_pair_union_fourth_card_le_seven
        V E1 E2 E3 E4 hVcard hE1card hE2card hE3card hE4card
          hE4sub h123 (by simpa only [Finset.inter_comm] using hinter34)
    have h132partition : (E1 ∪ E3) ∪ E2 = V := by
      rw [← h123]
      ext i
      simp only [Finset.mem_union]
      tauto
    have h134card : ((E1 ∪ E3) ∪ E4).card ≤ 7 :=
      partition_pair_union_fourth_card_le_seven
        V E1 E3 E2 E4 hVcard hE1card hE3card hE2card hE4card
          hE4sub h132partition (by
            simpa only [Finset.inter_comm] using hinter24)
    let line2 := secantParameter family gamma1 gamma4
    have hline2 : line2 ∈ lineParameters family :=
      secantParameter_mem_lineParameters family hgamma1G hgamma4G h14
    have h1On : gamma1 ∈ pointsOn family line2 :=
      first_point_mem_pointsOn_secant family hgamma1G
    have h4On : gamma4 ∈ pointsOn family line2 :=
      second_point_mem_pointsOn_secant family hgamma4G h14
    have h2On : gamma2 ∈ pointsOn family line2 := by
      apply third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
        family hn hsource hgamma1 hgamma4 hgamma2 h14 h12 hroot14 hroot12
      simpa only [E1, E2, E4, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using h124card.trans (by omega : 7 ≤ 8)
    have h3On : gamma3 ∈ pointsOn family line2 := by
      apply third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
        family hn hsource hgamma1 hgamma4 hgamma3 h14 h13 hroot14 hroot13
      simpa only [E1, E3, E4, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm] using h134card.trans (by omega : 7 ≤ 8)
    exact ⟨line2, hline2, h1On, h2On, h3On, h4On⟩
  · by_cases h124 : (E1 ∪ E2) ∪ E4 = V
    · have h123card : ((E1 ∪ E2) ∪ E3).card ≤ 8 :=
        union_card_le_eight_of_ne E1 E2 E3
          (Finset.union_subset (Finset.union_subset hE1sub hE2sub) hE3sub) h123
      have h142partition : (E1 ∪ E4) ∪ E2 = V := by
        rw [← h124]
        ext i
        simp only [Finset.mem_union]
        tauto
      have h143card : ((E1 ∪ E4) ∪ E3).card ≤ 7 :=
        partition_pair_union_fourth_card_le_seven
          V E1 E4 E2 E3 hVcard hE1card hE4card hE2card hE3card
            hE3sub h142partition (by
              simpa only [Finset.inter_comm] using hinter23)
      let line2 := secantParameter family gamma1 gamma3
      have hline2 : line2 ∈ lineParameters family :=
        secantParameter_mem_lineParameters family hgamma1G hgamma3G h13
      have h1On : gamma1 ∈ pointsOn family line2 :=
        first_point_mem_pointsOn_secant family hgamma1G
      have h3On : gamma3 ∈ pointsOn family line2 :=
        second_point_mem_pointsOn_secant family hgamma3G h13
      have h2On : gamma2 ∈ pointsOn family line2 := by
        apply third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
          family hn hsource hgamma1 hgamma3 hgamma2 h13 h12 hroot13 hroot12
        simpa only [E1, E2, E3, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using h123card
      have h4On : gamma4 ∈ pointsOn family line2 := by
        apply third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
          family hn hsource hgamma1 hgamma3 hgamma4 h13 h14 hroot13 hroot14
        simpa only [E1, E3, E4, Finset.union_assoc, Finset.union_left_comm,
          Finset.union_comm] using h143card.trans (by omega : 7 ≤ 8)
      exact ⟨line2, hline2, h1On, h2On, h3On, h4On⟩
    · have h123card : ((E1 ∪ E2) ∪ E3).card ≤ 8 :=
        union_card_le_eight_of_ne E1 E2 E3
          (Finset.union_subset (Finset.union_subset hE1sub hE2sub) hE3sub) h123
      have h124card : ((E1 ∪ E2) ∪ E4).card ≤ 8 :=
        union_card_le_eight_of_ne E1 E2 E4
          (Finset.union_subset (Finset.union_subset hE1sub hE2sub) hE4sub) h124
      let line2 := secantParameter family gamma1 gamma2
      have hline2 : line2 ∈ lineParameters family :=
        secantParameter_mem_lineParameters family hgamma1G hgamma2G h12
      have h1On : gamma1 ∈ pointsOn family line2 :=
        first_point_mem_pointsOn_secant family hgamma1G
      have h2On : gamma2 ∈ pointsOn family line2 :=
        second_point_mem_pointsOn_secant family hgamma2G h12
      have h3On : gamma3 ∈ pointsOn family line2 := by
        exact third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
          family hn hsource hgamma1 hgamma2 hgamma3 h12 h13
            hroot12 hroot13 (by simpa only [E1, E2, E3] using h123card)
      have h4On : gamma4 ∈ pointsOn family line2 := by
        exact third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
          family hn hsource hgamma1 hgamma2 hgamma4 h12 h14
            hroot12 hroot14 (by simpa only [E1, E2, E4] using h124card)
      exact ⟨line2, hline2, h1On, h2On, h3On, h4On⟩

/-! ## The four-point line is impossible -/

/-- Four regular outsiders with one source-root triple cannot exist in a
no-eight size-seven residual.  Their forced common line has core exactly
seven; removing its common four-coordinate fresh petal from any three fresh
six-sets leaves three disjoint two-sets in five coordinates. -/
theorem not_four_regular_same_root_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma1 gamma2 gamma3 gamma4 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family residual.source)
    (hgamma2 : gamma2 ∈ regularOutsideLine family residual.source)
    (hgamma3 : gamma3 ∈ regularOutsideLine family residual.source)
    (hgamma4 : gamma4 ∈ regularOutsideLine family residual.source)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (h14 : gamma1 ≠ gamma4) (h23 : gamma2 ≠ gamma3)
    (h24 : gamma2 ≠ gamma4) (h34 : gamma3 ≠ gamma4)
    (hroot12 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma2)
    (hroot13 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma3)
    (hroot14 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma4) : False := by
  obtain ⟨line2, hline2, h1On, h2On, h3On, h4On⟩ :=
    exists_line_of_four_regular_same_root_noEight_source_seven
      family hn residual hsource hgamma1 hgamma2 hgamma3 hgamma4
        h12 h13 h14 h23 h24 h34 hroot12 hroot13 hroot14
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let V : Finset I := Finset.univ \ D
  let P := D2 \ D
  let S1 := sourceFreshAgreement family residual.source gamma1
  let S2 := sourceFreshAgreement family residual.source gamma2
  let S3 := sourceFreshAgreement family residual.source gamma3
  have hD2cap : D2.card ≤ 7 := by
    simpa only [D2] using residual.global_core_cap line2 hline2
  have hfour : 4 ≤ (pointsOn family line2).card := by
    have hlt : 3 < (pointsOn family line2).card := by
      apply Finset.three_lt_card_iff.mpr
      exact ⟨gamma1, gamma2, gamma3, gamma4,
        h1On, h2On, h3On, h4On, h12, h13, h14, h23, h24, h34⟩
    omega
  have hpack := pointsOn_card_mul_max_add_core_le family hline2
  change (pointsOn family line2).card * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - D2.card) +
        D2.card ≤ Fintype.card I at hpack
  rw [hthreshold, hn] at hpack
  have hfactor : 9 - D2.card ≤ max 1 (9 - D2.card) := le_max_right _ _
  have hmul : 4 * (9 - D2.card) ≤
      (pointsOn family line2).card * max 1 (9 - D2.card) :=
    Nat.mul_le_mul hfour hfactor
  have hbase : 4 * (9 - D2.card) + D2.card ≤ 16 :=
    (Nat.add_le_add_right hmul D2.card).trans hpack
  have hD2card : D2.card = 7 := by omega
  have pair_core_eq (gamma beta : F) (hne : gamma ≠ beta)
      (hgammaOn : gamma ∈ pointsOn family line2)
      (hbetaOn : beta ∈ pointsOn family line2) :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        fullAgreement dom (u 0) (u 1) beta (family.q beta) = D2 := by
    have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
    have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
    dsimp only [D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have fresh_inter_eq (gamma beta : F) (hne : gamma ≠ beta)
      (hgammaOn : gamma ∈ pointsOn family line2)
      (hbetaOn : beta ∈ pointsOn family line2) :
      sourceFreshAgreement family residual.source gamma ∩
        sourceFreshAgreement family residual.source beta = P := by
    change sourceFreshAgreement family residual.source gamma ∩
      sourceFreshAgreement family residual.source beta = D2 \ D
    rw [← pair_core_eq gamma beta hne hgammaOn hbetaOn]
    ext i
    simp only [sourceFreshAgreement, P, D, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hS12 : S1 ∩ S2 = P := by
    simpa only [S1, S2] using fresh_inter_eq gamma1 gamma2 h12 h1On h2On
  have hS13 : S1 ∩ S3 = P := by
    simpa only [S1, S3] using fresh_inter_eq gamma1 gamma3 h13 h1On h3On
  have hS23 : S2 ∩ S3 = P := by
    simpa only [S2, S3] using fresh_inter_eq gamma2 gamma3 h23 h2On h3On
  have hrootEq :
      regularRootTriple family residual.source gamma1 ∩
        regularRootTriple family residual.source gamma2 = D2 ∩ D := by
    rw [← pair_core_eq gamma1 gamma2 h12 h1On h2On]
    ext i
    simp only [regularRootTriple, D, Finset.mem_inter]
    tauto
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  have hrootCard :
      (regularRootTriple family residual.source gamma1).card = 3 := by
    simpa only [regularRootTriple] using hgamma1Data.2.2.2
  have hrootInterCard :
      (regularRootTriple family residual.source gamma1 ∩
        regularRootTriple family residual.source gamma2).card = 3 := by
    rw [← hroot12, Finset.inter_self, hrootCard]
  have hD2interD : (D2 ∩ D).card = 3 := by
    rw [← hrootEq]
    exact hrootInterCard
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  have hPcard : P.card = 4 := by
    change (D2 \ D).card = 4
    omega
  have hVcard : V.card = 9 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hsource]
  have hS1sub : S1 ⊆ V := by
    simpa only [S1, V, D] using
      sourceFreshAgreement_subset_coreComplement family residual.source gamma1
  have hS2sub : S2 ⊆ V := by
    simpa only [S2, V, D] using
      sourceFreshAgreement_subset_coreComplement family residual.source gamma2
  have hS3sub : S3 ⊆ V := by
    simpa only [S3, V, D] using
      sourceFreshAgreement_subset_coreComplement family residual.source gamma3
  have hS1card : S1.card = 6 := by
    simpa only [S1] using hgamma1Data.2.1
  have hS2card : S2.card = 6 := by
    simpa only [S2] using hgamma2Data.2.1
  have hS3card : S3.card = 6 := by
    simpa only [S3] using hgamma3Data.2.1
  exact no_three_six_sets_with_common_four_intersection
    V P S1 S2 S3 hVcard hPcard hS1sub hS2sub hS3sub
      hS1card hS2card hS3card hS12 hS13 hS23

/-- **Fixed-root cap.**  A no-eight size-seven source has at most three
regular outsiders carrying any prescribed source-root triple. -/
theorem regularRootFiber_card_le_three_of_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    (T : Finset I) :
    (regularRootFiber family residual.source T).card ≤ 3 := by
  by_contra hnot
  have hfour : 3 < (regularRootFiber family residual.source T).card := by
    omega
  obtain ⟨gamma1, gamma2, gamma3, gamma4,
      hgamma1, hgamma2, hgamma3, hgamma4,
      h12, h13, h14, h23, h24, h34⟩ :=
    Finset.three_lt_card_iff.mp hfour
  simp only [regularRootFiber, Finset.mem_filter] at hgamma1
  simp only [regularRootFiber, Finset.mem_filter] at hgamma2
  simp only [regularRootFiber, Finset.mem_filter] at hgamma3
  simp only [regularRootFiber, Finset.mem_filter] at hgamma4
  have hroot12 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma2 :=
    hgamma1.2.trans hgamma2.2.symm
  have hroot13 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma3 :=
    hgamma1.2.trans hgamma3.2.symm
  have hroot14 : regularRootTriple family residual.source gamma1 =
      regularRootTriple family residual.source gamma4 :=
    hgamma1.2.trans hgamma4.2.symm
  exact not_four_regular_same_root_noEight_source_seven
    family hn hthreshold residual hsource
      hgamma1.1 hgamma2.1 hgamma3.1 hgamma4.1
      h12 h13 h14 h23 h24 h34 hroot12 hroot13 hroot14

/-- **All-outsider composition.**  Every outsider from a no-eight
size-seven source either lies in a regular cubic-locator fiber of cardinality
at most three, or its canonical missed support has cardinality at most two.
This is the direct interface between the all-outsider root/support law and
the fixed-root rigidity theorem. -/
theorem sourceSeven_outside_regularFiberCapped_or_missed_card_le_two
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family residual.source) :
    (∃ T : Finset I,
      gamma ∈ regularRootFiber family residual.source T ∧
        (regularRootFiber family residual.source T).card ≤ 3) ∨
      (sourceSevenMissedSet family residual.source gamma).card ≤ 2 := by
  rcases sourceSeven_regular_or_missed_card_le_two
      family hn hthreshold.ge residual.source_mem hsource hgamma with
    hregular | hsmall
  · apply Or.inl
    let T := regularRootTriple family residual.source gamma
    refine ⟨T, ?_, regularRootFiber_card_le_three_of_noEight_source_seven
      family hn hthreshold residual hsource T⟩
    simp only [regularRootFiber, Finset.mem_filter, T]
    exact ⟨hregular, trivial⟩
  · exact Or.inr hsmall

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootFiber

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootFiber
#print axioms no_three_six_sets_with_common_four_intersection
#print axioms partition_pair_union_fourth_card_le_seven
#print axioms regularMissedEdge_card_eq_three_of_source_seven
#print axioms root_inter_add_missed_inter_le_four_of_noEight_source_seven
#print axioms missed_inter_card_le_one_of_noEight_source_seven_same_root
#print axioms third_regular_mem_pointsOn_secant_of_same_root_of_common_fresh
#print axioms third_regular_mem_pointsOn_secant_of_same_root_of_missed_union_le_eight
#print axioms third_regular_mem_pointsOn_secant_of_root_missed_balance
#print axioms exists_line_of_four_regular_same_root_noEight_source_seven
#print axioms not_four_regular_same_root_noEight_source_seven
#print axioms regularRootFiber_card_le_three_of_noEight_source_seven
#print axioms sourceSeven_outside_regularFiberCapped_or_missed_card_le_two
