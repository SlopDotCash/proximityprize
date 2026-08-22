/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourRegularSignatureRigidity

/-!
# Rate-quarter `n = 16`, `k = 4`: signatures under a unique eight-core

This file consumes the unique-eight-core branch of the global core
classification.  A regular outsider has a three-subset `T` of the source core
and a missed two-subset `E` of its complement.  For two distinct regular
outsiders, their secant core has cardinality

`4 + |T1 ∩ T2| + |E1 ∩ E2|`.

Uniqueness of the relevant eight-core therefore forces
`|T1 ∩ T2| + |E1 ∩ E2| <= 3`.  Equal root triples consequently have
disjoint missed edges.  Three outsiders in one root fiber would have three
pairwise-disjoint missed edges, contradicting the affine-row filling theorem.
Thus every root-triple fiber has size at most two, and the eight regular
outsiders in the residual use at least four distinct root triples.

These are genuine signature restrictions, not a closure of the unique-core
branch: the resulting abstract signature system still admits eight elements.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The regular outsiders carrying a prescribed source-core root triple. -/
noncomputable def regularRootFiber
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (T : Finset I) : Finset F :=
  (regularOutsideLine family line).filter fun gamma =>
    regularRootTriple family line gamma = T

/-- The root triples used by the regular-outsider population. -/
noncomputable def regularRootImage
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : Finset (Finset I) :=
  (regularOutsideLine family line).image fun gamma =>
    regularRootTriple family line gamma

/-- The fresh intersection of two regular outsiders has size four plus the
intersection size of their missed edges. -/
theorem regular_fresh_inter_card_eq_four_add_missed_inter
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line) :
    (sourceFreshAgreement family line gamma ∩
        sourceFreshAgreement family line beta).card =
      4 + (regularMissedEdge family line gamma ∩
        regularMissedEdge family line beta).card := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let Sg := sourceFreshAgreement family line gamma
  let Sb := sourceFreshAgreement family line beta
  let Eg := regularMissedEdge family line gamma
  let Eb := regularMissedEdge family line beta
  have hVcard : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hSgsub : Sg ⊆ V := by
    simpa only [Sg, V, D] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hSbsub : Sb ⊆ V := by
    simpa only [Sb, V, D] using
      sourceFreshAgreement_subset_coreComplement family line beta
  have hEg : Eg = V \ Sg := by
    rfl
  have hEb : Eb = V \ Sb := by
    rfl
  have hSg : Sg = V \ Eg := by
    rw [hEg]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      exact ⟨hSgsub hi, fun hnot ↦ hnot.2 hi⟩
    · rintro ⟨hiV, hi⟩
      by_contra hnot
      exact hi ⟨hiV, hnot⟩
  have hSb : Sb = V \ Eb := by
    rw [hEb]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      exact ⟨hSbsub hi, fun hnot ↦ hnot.2 hi⟩
    · rintro ⟨hiV, hi⟩
      by_contra hnot
      exact hi ⟨hiV, hnot⟩
  have hEgc := (regular_signature_cardinalities family hn hcore hgamma).2
  have hEbc := (regular_signature_cardinalities family hn hcore hbeta).2
  change Eg.card = 2 at hEgc
  change Eb.card = 2 at hEbc
  have hEgunionSub : Eg ∪ Eb ⊆ V := by
    rw [hEg, hEb]
    exact Finset.union_subset Finset.sdiff_subset Finset.sdiff_subset
  have hfreshEq : Sg ∩ Sb = V \ (Eg ∪ Eb) := by
    rw [hSg, hSb]
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hpartition := Finset.card_sdiff_add_card_inter V (Eg ∪ Eb)
  have hinter : V ∩ (Eg ∪ Eb) = Eg ∪ Eb := by
    exact Finset.inter_eq_right.mpr hEgunionSub
  have hunion := Finset.card_union_add_card_inter Eg Eb
  change (Sg ∩ Sb).card = 4 + (Eg ∩ Eb).card
  rw [hfreshEq]
  rw [hinter] at hpartition
  omega

/-- Under uniqueness of the source eight-core, two distinct regular
signatures have total root/missed-edge intersection at most three. -/
theorem root_inter_add_missed_inter_le_three_of_unique_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hunique : ∀ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card →
        line2 = line)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line)
    (hne : gamma ≠ beta) :
    (regularRootTriple family line gamma ∩
        regularRootTriple family line beta).card +
      (regularMissedEdge family line gamma ∩
        regularMissedEdge family line beta).card ≤ 3 := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let Tg := regularRootTriple family line gamma
  let Tb := regularRootTriple family line beta
  let Sg := sourceFreshAgreement family line gamma
  let Sb := sourceFreshAgreement family line beta
  have hgammaData := hgamma
  have hbetaData := hbeta
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData hbetaData
  have hgammaOut := (mem_outsideLine_iff family line gamma).mp hgammaData.1
  have hbetaOut := (mem_outsideLine_iff family line beta).mp hbetaData.1
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
  have hlineNe : line2 ≠ line := by
    intro heq
    have hgammaSource : gamma ∈ pointsOn family line := by
      rw [← heq]
      exact hgammaOn
    have hq := (mem_pointsOn_iff family line gamma).mp hgammaSource |>.2
    exact hgammaOut.2 hq
  have hD2lt : D2.card < 8 := by
    by_contra hnot
    have hlarge :
        8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
      simpa only [D2] using (show 8 ≤ D2.card by omega)
    exact hlineNe (hunique line2 hline2 hlarge)
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
  have hfreshCard := regular_fresh_inter_card_eq_four_add_missed_inter
    family hn hcore hgamma hbeta
  change (Tg ∩ Tb).card +
      (regularMissedEdge family line gamma ∩
        regularMissedEdge family line beta).card ≤ 3
  rw [hfreshEq] at hfreshCard
  rw [hrootEq]
  have hsplit' : (D2 \ D).card + (D ∩ D2).card = D2.card := by
    simpa only [Finset.inter_comm D D2] using hsplit
  omega

/-- Equal-root regular outsiders must have disjoint missed edges. -/
theorem missedEdges_disjoint_of_same_root_of_unique_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hunique : ∀ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card →
        line2 = line)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line)
    (hne : gamma ≠ beta)
    (hroot : regularRootTriple family line gamma =
      regularRootTriple family line beta) :
    Disjoint (regularMissedEdge family line gamma)
      (regularMissedEdge family line beta) := by
  have hsum := root_inter_add_missed_inter_le_three_of_unique_core
    family hn hcore hunique hgamma hbeta hne
  have hrootCard := (regular_signature_cardinalities
    family hn hcore hgamma).1
  have hinterRoot :
      (regularRootTriple family line gamma ∩
        regularRootTriple family line beta).card = 3 := by
    rw [← hroot, Finset.inter_self, hrootCard]
  have hinterMiss :
      (regularMissedEdge family line gamma ∩
        regularMissedEdge family line beta).card = 0 := by
    omega
  exact Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.card_eq_zero.mp hinterMiss)

/-- Every regular root-triple fiber has multiplicity at most two under a
unique relevant eight-core. -/
theorem regularRootFiber_card_le_two_of_unique_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hunique : ∀ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card →
        line2 = line)
    (T : Finset I) :
    (regularRootFiber family line T).card ≤ 2 := by
  by_contra hnot
  have hthree : 2 < (regularRootFiber family line T).card := by omega
  obtain ⟨gamma1, gamma2, gamma3, hgamma1, hgamma2, hgamma3,
      hgamma12, hgamma13, hgamma23⟩ :=
    Finset.two_lt_card_iff.mp hthree
  simp only [regularRootFiber, Finset.mem_filter] at hgamma1 hgamma2 hgamma3
  have hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2 :=
    hgamma1.2.trans hgamma2.2.symm
  have hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3 :=
    hgamma1.2.trans hgamma3.2.symm
  have hdis12 := missedEdges_disjoint_of_same_root_of_unique_core
    family hn hcore hunique hgamma1.1 hgamma2.1 hgamma12 hroot12
  have hdis13 := missedEdges_disjoint_of_same_root_of_unique_core
    family hn hcore hunique hgamma1.1 hgamma3.1 hgamma13 hroot13
  have hdis23 := missedEdges_disjoint_of_same_root_of_unique_core
    family hn hcore hunique hgamma2.1 hgamma3.1 hgamma23
      (hroot12.symm.trans hroot13)
  exact not_pairwise_disjoint_missedEdges_of_three_regular_same_rootTriple
    family hn hline hcore hgamma1.1 hgamma2.1 hgamma3.1
      hgamma12 hgamma13 hgamma23 hroot12 hroot13
      ⟨hdis12, hdis13, hdis23⟩

/-- The regular population is at most twice its root-triple image. -/
theorem regularOutsideLine_card_le_two_mul_regularRootImage
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hunique : ∀ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card →
        line2 = line) :
    (regularOutsideLine family line).card ≤
      2 * (regularRootImage family line).card := by
  have hbound := Finset.card_le_mul_card_image
    (regularOutsideLine family line) 2 (fun T _hT =>
      regularRootFiber_card_le_two_of_unique_core
        family hn hline hcore hunique T)
  simpa only [regularRootFiber, regularRootImage] using hbound

/-- The unique-eight-core residual has at least four distinct regular root
triples. -/
theorem four_le_regularRootImage_card_of_residual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family) :
    4 ≤ (regularRootImage family residual.source).card := by
  have hbound := regularOutsideLine_card_le_two_mul_regularRootImage
    family hn residual.source_mem residual.source_core_card
      residual.source_unique
  have hpopulation := residual.eight_regular_outsiders
  omega

/-! ## The exact three-hole secant -/

/-- The distinguished sub-high secant carried by the unique-core residual. -/
noncomputable def residualSecantLine
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) : LineParameter F :=
  secantParameter family residual.gamma residual.beta

/-- Regular outsiders not lying on the distinguished sub-high secant. -/
noncomputable def regularOffResidualSecant
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) : Finset F :=
  regularOutsideLine family residual.source \
    pointsOn family (residualSecantLine residual)

/-- The distinguished secant contains at most four selected points.  The
bound follows directly from exact fresh-fibre packing for its core size
`5`, `6`, or `7`. -/
theorem residualSecant_pointsOn_card_le_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family) :
    (pointsOn family (residualSecantLine residual)).card ≤ 4 := by
  let line2 := residualSecantLine residual
  let z := (jointCore dom (u 0) (u 1) line2.1 line2.2).card
  let L := (pointsOn family line2).card
  have hzForm : z = 5 +
      (jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
    simpa only [z, line2, residualSecantLine] using
      residual.secant_core_card
  have hinter :
      (jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 2 := by
    simpa only [line2, residualSecantLine] using
      residual.source_secant_inter_card_le_two
  have hzLower : 5 ≤ z := by omega
  have hzUpper : z ≤ 7 := by omega
  have hline2 : line2 ∈ lineParameters family := by
    simpa only [line2, residualSecantLine] using residual.secant_mem
  have hpack := pointsOn_card_mul_max_add_core_le family hline2
  change L * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) + z ≤
    Fintype.card I at hpack
  rw [hthreshold, hn] at hpack
  change L ≤ 4
  interval_cases z <;> norm_num at hpack ⊢ <;> omega

/-- At least four regular outsiders lie off the distinguished sub-high
secant. -/
theorem four_le_regularOffResidualSecant_card
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family) :
    4 ≤ (regularOffResidualSecant family residual).card := by
  let R := regularOutsideLine family residual.source
  let L := pointsOn family (residualSecantLine residual)
  have hpopulation : 8 ≤ R.card := by
    simpa only [R] using residual.eight_regular_outsiders
  have hline : L.card ≤ 4 := by
    simpa only [L] using
      residualSecant_pointsOn_card_le_four family hn hthreshold residual
  have hsplit := Finset.card_sdiff_add_card_inter R L
  have hinter : (R ∩ L).card ≤ L.card :=
    Finset.card_le_card Finset.inter_subset_right
  change 4 ≤ (R \ L).card
  omega

/-- Every regular outsider off the distinguished secant has the exact
three-hole signature forced by the residual geometry:

* its source-root triple avoids the source/secant core overlap;
* its missed edge lies inside the five-coordinate secant petal; and
* all three coordinates uncovered by the two cores are fresh agreements.
-/
theorem offResidualSecant_signature_restrictions
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual) :
    Disjoint
        (regularRootTriple family residual.source theta)
        (jointCore dom (u 0) (u 1)
            residual.source.1 residual.source.2 ∩
          jointCore dom (u 0) (u 1)
            (residualSecantLine residual).1
            (residualSecantLine residual).2) ∧
      regularMissedEdge family residual.source theta ⊆
        jointCore dom (u 0) (u 1)
            (residualSecantLine residual).1
            (residualSecantLine residual).2 \
          jointCore dom (u 0) (u 1)
            residual.source.1 residual.source.2 ∧
      Finset.univ \ (
          jointCore dom (u 0) (u 1)
              residual.source.1 residual.source.2 ∪
            jointCore dom (u 0) (u 1)
              (residualSecantLine residual).1
              (residualSecantLine residual).2) ⊆
        sourceFreshAgreement family residual.source theta := by
  let line := residual.source
  let line2 := residualSecantLine residual
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let C0 := D ∩ D2
  let P := D2 \ D
  let H := Finset.univ \ (D ∪ D2)
  let A := fullAgreement dom (u 0) (u 1) theta (family.q theta)
  let T := regularRootTriple family line theta
  let S := sourceFreshAgreement family line theta
  let E := regularMissedEdge family line theta
  have hthetaData := htheta
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData
  have hregular := hthetaData.1
  have hnotOn := hthetaData.2
  have hregularData := hregular
  simp only [regularOutsideLine, Finset.mem_filter] at hregularData
  have hthetaOut :=
    (mem_outsideLine_iff family line theta).mp hregularData.1
  have hline2 : line2 ∈ lineParameters family := by
    simpa only [line2, residualSecantLine] using residual.secant_mem
  have hline2Deg := lineParameter_degree_lt family hline2
  have hqNe : family.q theta ≠ line2.1 + C theta * line2.2 := by
    intro hq
    apply hnotOn
    exact (mem_pointsOn_iff family line2 theta).mpr ⟨hthetaOut.1, hq⟩
  have hcap := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) (k := 4) (by norm_num)
      (family.degree_lt theta hthetaOut.1)
      hline2Deg.1 hline2Deg.2 hqNe
  have hcap' : (A ∩ D2).card ≤ 3 := by
    norm_num at hcap
    simpa only [A, D2] using hcap
  have hPcard : P.card = 5 := by
    simpa only [P, D, D2, line, line2, residualSecantLine,
      secantPetal] using residual.secant_petal_card
  have hEcard : E.card = 2 := by
    simpa only [E, line] using
      (regular_signature_cardinalities
        family hn residual.source_core_card hregular).2
  have hSsub : S ⊆ Finset.univ \ D := by
    simpa only [S, D, line] using
      sourceFreshAgreement_subset_coreComplement family line theta
  have hPsub : P ⊆ Finset.univ \ D := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hPminusSSubE : P \ S ⊆ E := by
    intro i hi
    have hiP := (Finset.mem_sdiff.mp hi).1
    have hiS := (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨hPsub hiP, hiS⟩
  have hPminusSCard : (P \ S).card ≤ 2 := by
    exact (Finset.card_le_card hPminusSSubE).trans_eq hEcard
  have hPsplit := Finset.card_sdiff_add_card_inter P S
  have hSPcardLower : 3 ≤ (S ∩ P).card := by
    rw [Finset.inter_comm]
    omega
  have hOutsideEq : (A ∩ D2) \ D = S ∩ P := by
    ext i
    simp only [A, D2, D, S, P, sourceFreshAgreement,
      Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hInsideEq : (A ∩ D2) ∩ D = T ∩ C0 := by
    ext i
    simp only [A, D2, D, T, C0, regularRootTriple,
      Finset.mem_inter]
    tauto
  have hAD2split := Finset.card_sdiff_add_card_inter (A ∩ D2) D
  rw [hOutsideEq, hInsideEq] at hAD2split
  have hSPcard : (S ∩ P).card = 3 := by omega
  have hTCcard : (T ∩ C0).card = 0 := by omega
  have hPminusSCardEq : (P \ S).card = 2 := by
    rw [Finset.inter_comm] at hPsplit
    omega
  have hPminusSEq : P \ S = E := by
    apply Finset.eq_of_subset_of_card_le hPminusSSubE
    omega
  have hEsubP : E ⊆ P := by
    rw [← hPminusSEq]
    exact Finset.sdiff_subset
  have hHsubS : H ⊆ S := by
    intro i hiH
    have hiData := Finset.mem_sdiff.mp hiH
    have hiD : i ∉ D := by
      intro hiD
      exact hiData.2 (Finset.mem_union_left _ hiD)
    have hiD2 : i ∉ D2 := by
      intro hiD2
      exact hiData.2 (Finset.mem_union_right _ hiD2)
    have hiV : i ∈ Finset.univ \ D :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiD⟩
    by_contra hiS
    have hiE : i ∈ E := Finset.mem_sdiff.mpr ⟨hiV, hiS⟩
    exact hiD2 ((Finset.mem_sdiff.mp (hEsubP hiE)).1)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [T, C0, D, D2, line, line2] using
      Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.card_eq_zero.mp hTCcard)
  · simpa only [E, P, D, D2, line, line2] using hEsubP
  · simpa only [H, S, D, D2, line, line2] using hHsubS

/-- The three residual holes lie in the secant core of every pair of
distinct regular outsiders off the distinguished secant.  Thus the surviving
off-secant population is a shared-three-anchor configuration. -/
theorem residual_holes_subset_pair_secant_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi) :
    Finset.univ \ (
        jointCore dom (u 0) (u 1)
            residual.source.1 residual.source.2 ∪
          jointCore dom (u 0) (u 1)
            (residualSecantLine residual).1
            (residualSecantLine residual).2) ⊆
      jointCore dom (u 0) (u 1)
        (secantParameter family theta phi).1
        (secantParameter family theta phi).2 := by
  let H := Finset.univ \ (
    jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
      jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2)
  let line3 := secantParameter family theta phi
  have hthetaRestrict :=
    (offResidualSecant_signature_restrictions
      family hn residual htheta).2.2
  have hphiRestrict :=
    (offResidualSecant_signature_restrictions
      family hn residual hphi).2.2
  have hthetaData := htheta
  have hphiData := hphi
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData hphiData
  have hthetaRegular := hthetaData.1
  have hphiRegular := hphiData.1
  have hthetaRegularData := hthetaRegular
  have hphiRegularData := hphiRegular
  simp only [regularOutsideLine, Finset.mem_filter] at hthetaRegularData hphiRegularData
  have hthetaG :=
    (mem_outsideLine_iff family residual.source theta).mp
      hthetaRegularData.1 |>.1
  have hphiG :=
    (mem_outsideLine_iff family residual.source phi).mp
      hphiRegularData.1 |>.1
  have hline3 : line3 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hthetaG hphiG hne
  have hthetaOn : theta ∈ pointsOn family line3 :=
    first_point_mem_pointsOn_secant family hthetaG
  have hphiOn : phi ∈ pointsOn family line3 :=
    second_point_mem_pointsOn_secant family hphiG hne
  have hthetaEq := (mem_pointsOn_iff family line3 theta).mp hthetaOn |>.2
  have hphiEq := (mem_pointsOn_iff family line3 phi).mp hphiOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
          fullAgreement dom (u 0) (u 1) phi (family.q phi) =
        jointCore dom (u 0) (u 1) line3.1 line3.2 := by
    rw [hthetaEq, hphiEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line3.1 line3.2 hne
  intro i hiH
  have hiThetaFresh :
      i ∈ sourceFreshAgreement family residual.source theta :=
    hthetaRestrict (by simpa only [H] using hiH)
  have hiPhiFresh :
      i ∈ sourceFreshAgreement family residual.source phi :=
    hphiRestrict (by simpa only [H] using hiH)
  rw [← hcoreEq]
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_sdiff.mp hiThetaFresh).1,
      (Finset.mem_sdiff.mp hiPhiFresh).1⟩

/-- Every pair secant in the surviving off-secant population has a core of
size between three and seven.  The lower bound is the common residual-hole
anchor; the upper bound is uniqueness of the source eight-core. -/
theorem offResidualSecant_pair_core_band
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi) :
    3 ≤ (jointCore dom (u 0) (u 1)
        (secantParameter family theta phi).1
        (secantParameter family theta phi).2).card ∧
      (jointCore dom (u 0) (u 1)
        (secantParameter family theta phi).1
        (secantParameter family theta phi).2).card ≤ 7 := by
  let H := Finset.univ \ (
    jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
      jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2)
  let line3 := secantParameter family theta phi
  let D3 := jointCore dom (u 0) (u 1) line3.1 line3.2
  have hHcard : H.card = 3 := by
    simpa only [H, residualSecantLine] using residual.uncovered_card
  have hHsub : H ⊆ D3 := by
    simpa only [H, D3, line3] using
      residual_holes_subset_pair_secant_core
        family hn residual htheta hphi hne
  have hlower : 3 ≤ D3.card := by
    rw [← hHcard]
    exact Finset.card_le_card hHsub
  have hthetaData := htheta
  have hphiData := hphi
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData hphiData
  have hthetaRegularData := hthetaData.1
  have hphiRegularData := hphiData.1
  simp only [regularOutsideLine, Finset.mem_filter] at hthetaRegularData hphiRegularData
  have hthetaOut :=
    (mem_outsideLine_iff family residual.source theta).mp
      hthetaRegularData.1
  have hphiOut :=
    (mem_outsideLine_iff family residual.source phi).mp
      hphiRegularData.1
  have hline3Mem : line3 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hthetaOut.1 hphiOut.1 hne
  have hthetaOn : theta ∈ pointsOn family line3 :=
    first_point_mem_pointsOn_secant family hthetaOut.1
  have hline3Ne : line3 ≠ residual.source := by
    intro heq
    have hthetaSource : theta ∈ pointsOn family residual.source := by
      rw [← heq]
      exact hthetaOn
    exact hthetaOut.2
      ((mem_pointsOn_iff family residual.source theta).mp hthetaSource |>.2)
  have hupper : D3.card ≤ 7 := by
    by_contra hnot
    have hlarge :
        8 ≤ (jointCore dom (u 0) (u 1) line3.1 line3.2).card := by
      simpa only [D3] using (show 8 ≤ D3.card by omega)
    exact hline3Ne (residual.source_unique line3 hline3Mem hlarge)
  exact ⟨by simpa only [D3] using hlower,
    by simpa only [D3] using hupper⟩

/-! ## Cardinal-only sharpness -/

/-- Four triples on six coordinates, any two meeting in exactly one
coordinate. -/
def tetrahedralRootTriple : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

/-- Two disjoint missed edges inside a five-coordinate petal. -/
def twinMissedEdge : Fin 2 → Finset (Fin 5) :=
  ![{0, 1}, {2, 3}]

/-- **The proved signature restrictions alone still permit eight elements.**

Index signatures by `Fin 4 × Fin 2`, using the four tetrahedral root triples
and the two disjoint missed edges.  Every root triple has multiplicity exactly
two.  For distinct signatures, the root-intersection plus missed-edge-
intersection budget is at most three: it is `1 + 2` within one edge copy,
`3 + 0` for the two copies of one root, and `1 + 0` otherwise.

This finite countermodel shows that a closure of the unique-core branch needs
an additional polynomial compatibility among different root triples. -/
theorem eight_abstract_unique_core_signatures_exist :
    (Finset.univ : Finset (Fin 4 × Fin 2)).card = 8 ∧
      (∀ x : Fin 4 × Fin 2,
        (tetrahedralRootTriple x.1).card = 3 ∧
          (twinMissedEdge x.2).card = 2) ∧
      (∀ x y : Fin 4 × Fin 2, x ≠ y →
        (tetrahedralRootTriple x.1 ∩
            tetrahedralRootTriple y.1).card +
          (twinMissedEdge x.2 ∩ twinMissedEdge y.2).card ≤ 3) ∧
      (∀ a : Fin 4,
        ((Finset.univ : Finset (Fin 4 × Fin 2)).filter fun x =>
          tetrahedralRootTriple x.1 = tetrahedralRootTriple a).card = 2) := by
  decide

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
#print axioms regular_fresh_inter_card_eq_four_add_missed_inter
#print axioms root_inter_add_missed_inter_le_three_of_unique_core
#print axioms missedEdges_disjoint_of_same_root_of_unique_core
#print axioms regularRootFiber_card_le_two_of_unique_core
#print axioms regularOutsideLine_card_le_two_mul_regularRootImage
#print axioms four_le_regularRootImage_card_of_residual
#print axioms residualSecant_pointsOn_card_le_four
#print axioms four_le_regularOffResidualSecant_card
#print axioms offResidualSecant_signature_restrictions
#print axioms residual_holes_subset_pair_secant_core
#print axioms offResidualSecant_pair_core_band
#print axioms eight_abstract_unique_core_signatures_exist
