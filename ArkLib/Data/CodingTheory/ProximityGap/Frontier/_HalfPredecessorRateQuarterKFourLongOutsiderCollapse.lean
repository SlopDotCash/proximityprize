/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterComplementaryCores

/-!
# Rate-quarter `k = 4`: large-fresh outsider collapse

Fix a relevant decoded line with an eight-coordinate core in a sixteen-
coordinate domain.  Two outsiders with at least seven fresh agreements have
fresh intersection at least six inside the eight-coordinate core complement.
Their secant core therefore covers at least six coordinates outside the
source core, so the two cores miss at most two coordinates.  The saturated
complementary-core theorem then gives `|G| <= 16`.

Consequently, in a family larger than sixteen:

* at most one outsider has at least seven fresh agreements;
* at most one outsider has at least ten full agreements, since the off-line
  root cap converts ten full agreements into seven fresh agreements; and
* at least eight outsiders have exactly six fresh agreements.  For each of
  these regular outsiders, all inequalities saturate: it has exactly nine
  full agreements and exactly three agreements inside the source core.
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

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Agreements of an outside point away from the fixed source-line core. -/
noncomputable def sourceFreshAgreement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) : Finset I :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
    jointCore dom (u 0) (u 1) line.1 line.2

/-- Outsiders with at least `t` fresh agreements beyond the source core. -/
noncomputable def outsideLineFreshAtLeast
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (t : Nat) : Finset F :=
  (outsideLine family line).filter fun gamma =>
    t ≤ (sourceFreshAgreement family line gamma).card

/-- Outsiders with at least `t` full agreements. -/
noncomputable def outsideLineAtLeast
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (t : Nat) : Finset F :=
  (outsideLine family line).filter fun gamma =>
    t ≤ (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card

/-- The saturated outsider stratum: six fresh agreements, nine full
agreements, and three agreements in the source core. -/
noncomputable def regularOutsideLine
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : Finset F :=
  (outsideLine family line).filter fun gamma =>
    (sourceFreshAgreement family line gamma).card = 6 ∧
      (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card = 9 ∧
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        jointCore dom (u 0) (u 1) line.1 line.2).card = 3

@[simp]
theorem mem_outsideLineFreshAtLeast_iff
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (t : Nat) (gamma : F) :
    gamma ∈ outsideLineFreshAtLeast family line t ↔
      gamma ∈ outsideLine family line ∧
        t ≤ (sourceFreshAgreement family line gamma).card := by
  simp only [outsideLineFreshAtLeast, Finset.mem_filter]

@[simp]
theorem mem_outsideLineAtLeast_iff
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (t : Nat) (gamma : F) :
    gamma ∈ outsideLineAtLeast family line t ↔
      gamma ∈ outsideLine family line ∧
        t ≤ (fullAgreement dom (u 0) (u 1) gamma
          (family.q gamma)).card := by
  simp only [outsideLineAtLeast, Finset.mem_filter]

/-- Every outsider has at least six fresh agreements and at most three
agreements inside the source core. -/
theorem six_le_fresh_and_core_inter_le_three_of_outside
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    6 ≤ (sourceFreshAgreement family line gamma).card ∧
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 := by
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hdeg := lineParameter_degree_lt family hline
  have hinter := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) (k := 4) (by norm_num)
      (family.degree_lt gamma hgammaData.1) hdeg.1 hdeg.2 hgammaData.2
  have hinter' :
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
        jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 := by
    norm_num at hinter ⊢
    exact hinter
  have hlarge := hthreshold.trans
    (family.threshold_le gamma hgammaData.1)
  have hsplit := Finset.card_sdiff_add_card_inter
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (jointCore dom (u 0) (u 1) line.1 line.2)
  constructor
  · simp only [sourceFreshAgreement]
    omega
  · exact hinter'

/-- Ten full agreements force at least seven fresh agreements. -/
theorem seven_le_fresh_of_ten_le_fullAgreement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hlong : 10 ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card) :
    7 ≤ (sourceFreshAgreement family line gamma).card := by
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hdeg := lineParameter_degree_lt family hline
  have hinter := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) (k := 4) (by norm_num)
      (family.degree_lt gamma hgammaData.1) hdeg.1 hdeg.2 hgammaData.2
  have hsplit := Finset.card_sdiff_add_card_inter
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (jointCore dom (u 0) (u 1) line.1 line.2)
  simp only [sourceFreshAgreement]
  norm_num at hinter
  omega

/-- **Two fresh-seven outsiders force the domain bound.**  Their secant core
covers at least six of the eight coordinates outside the source core, so the
two-core complement has size at most two. -/
theorem card_le_sixteen_of_two_fresh_seven_outsiders
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family line)
    (hbeta : beta ∈ outsideLine family line) (hne : gamma ≠ beta)
    (hfreshGamma : 7 ≤ (sourceFreshAgreement family line gamma).card)
    (hfreshBeta : 7 ≤ (sourceFreshAgreement family line beta).card) :
    family.G.card ≤ 16 := by
  let line2 := secantParameter family gamma beta
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let X := sourceFreshAgreement family line gamma
  let Y := sourceFreshAgreement family line beta
  let V : Finset I := Finset.univ \ D
  let R : Finset I := Finset.univ \ (D ∪ D2)
  have hDcard : D.card = 8 := by simpa only [D] using hcore
  have hVcard : V.card = 8 := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hDcard]
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hbetaData := (mem_outsideLine_iff family line beta).mp hbeta
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.1 hbetaData.1 hne
  have hgammaOn : gamma ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgammaData.1
  have hbetaOn : beta ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hbetaData.1 hne
  have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) = D2 := by
    dsimp only [D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have hXY : X ∩ Y = D2 \ D := by
    calc
      X ∩ Y =
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta)) \ D := by
        ext i
        simp only [X, Y, sourceFreshAgreement, Finset.mem_inter,
          Finset.mem_sdiff]
        tauto
      _ = D2 \ D := by rw [hcoreEq]
  have hXsub : X ⊆ V := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hYsub : Y ⊆ V := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hunionSub : X ∪ Y ⊆ V := Finset.union_subset hXsub hYsub
  have hunionCard : (X ∪ Y).card ≤ 8 :=
    (Finset.card_le_card hunionSub).trans_eq hVcard
  have hunionInter := Finset.card_union_add_card_inter X Y
  change 7 ≤ X.card at hfreshGamma
  change 7 ≤ Y.card at hfreshBeta
  have hpetal : 6 ≤ (D2 \ D).card := by
    rw [← hXY]
    omega
  have hRform : R = V \ D2 := by
    ext i
    simp only [R, V, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_union]
    tauto
  have hinterForm : D2 ∩ V = D2 \ D := by
    ext i
    simp only [V, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
  have hRcard : R.card = 8 - (D2 \ D).card := by
    rw [hRform, Finset.card_sdiff, hinterForm, hVcard]
  have hmissing : R.card ≤ 2 := by omega
  have hn8 : Fintype.card I = 2 * 8 := by omega
  have hle := card_le_two_mul_of_saturated_small_complement
    family (k := 4) (h := 8) (by norm_num) (by norm_num)
      hn8 hthreshold line line2 hline hline2
      (by simpa only [R, D, D2, line2] using hmissing)
  norm_num at hle ⊢
  exact hle

/-- A counterexample has at most one outsider with seven fresh agreements. -/
theorem outsideLineFreshAtLeast_seven_card_le_one_of_card_gt_sixteen
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8) :
    (outsideLineFreshAtLeast family line 7).card ≤ 1 := by
  by_contra hnot
  have htwo : 1 < (outsideLineFreshAtLeast family line 7).card := by omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne⟩ :=
    Finset.one_lt_card.mp htwo
  have hgammaData := (mem_outsideLineFreshAtLeast_iff
    family line 7 gamma).mp hgamma
  have hbetaData := (mem_outsideLineFreshAtLeast_iff
    family line 7 beta).mp hbeta
  have hle := card_le_sixteen_of_two_fresh_seven_outsiders
    family hn hthreshold hline hcore hgammaData.1 hbetaData.1 hne
      hgammaData.2 hbetaData.2
  omega

/-- Hence a counterexample has at most one outsider with ten full
agreements. -/
theorem outsideLineAtLeast_ten_card_le_one_of_card_gt_sixteen
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8) :
    (outsideLineAtLeast family line 10).card ≤ 1 := by
  have hsub : outsideLineAtLeast family line 10 ⊆
      outsideLineFreshAtLeast family line 7 := by
    intro gamma hgamma
    have hgammaData := (mem_outsideLineAtLeast_iff
      family line 10 gamma).mp hgamma
    exact (mem_outsideLineFreshAtLeast_iff
      family line 7 gamma).mpr
        ⟨hgammaData.1,
          seven_le_fresh_of_ten_le_fullAgreement
            family hline hgammaData.1 hgammaData.2⟩
  exact (Finset.card_le_card hsub).trans
    (outsideLineFreshAtLeast_seven_card_le_one_of_card_gt_sixteen
      family hn hthreshold hcard hline hcore)

/-- **Regular-outsider population.**  In a counterexample, at least eight
outsiders saturate the threshold/root-cap split as `9 = 6 + 3`. -/
theorem eight_le_regularOutsideLine_card_of_card_gt_sixteen
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8) :
    8 ≤ (regularOutsideLine family line).card := by
  let large := outsideLineFreshAtLeast family line 7
  let small := outsideLine family line \ large
  have hlineCap := pointsOn_card_le_half
    family (h := 8) (by omega) hthreshold hline
  have hpartition := pointsOn_card_add_outsideLine_card family line
  have houtside : 9 ≤ (outsideLine family line).card := by omega
  have hlarge : large.card ≤ 1 := by
    simpa only [large] using
      (outsideLineFreshAtLeast_seven_card_le_one_of_card_gt_sixteen
        family hn hthreshold hcard hline hcore)
  have hlargeSub : large ⊆ outsideLine family line := by
    intro gamma hgamma
    exact (mem_outsideLineFreshAtLeast_iff
      family line 7 gamma).mp (by simpa only [large] using hgamma) |>.1
  have hsmallCard : small.card =
      (outsideLine family line).card - large.card := by
    simpa only [small] using Finset.card_sdiff_of_subset hlargeSub
  have hsmallSub : small ⊆ regularOutsideLine family line := by
    intro gamma hgamma
    have hgammaData := Finset.mem_sdiff.mp hgamma
    have hgammaOut : gamma ∈ outsideLine family line := hgammaData.1
    have hnotLarge : gamma ∉ large := hgammaData.2
    have hsixCap := six_le_fresh_and_core_inter_le_three_of_outside
      family hthreshold hline hgammaOut
    have hnotSeven : ¬ 7 ≤
        (sourceFreshAgreement family line gamma).card := by
      intro hseven
      apply hnotLarge
      simpa only [large] using
        (mem_outsideLineFreshAtLeast_iff
          family line 7 gamma).mpr ⟨hgammaOut, hseven⟩
    have hfresh : (sourceFreshAgreement family line gamma).card = 6 := by
      omega
    have hgammaG := (mem_outsideLine_iff family line gamma).mp hgammaOut |>.1
    have hfullLower := hthreshold.trans
      (family.threshold_le gamma hgammaG)
    have hsplit := Finset.card_sdiff_add_card_inter
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
      (jointCore dom (u 0) (u 1) line.1 line.2)
    have hsplit' :
        (sourceFreshAgreement family line gamma).card +
            (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
              jointCore dom (u 0) (u 1) line.1 line.2).card =
          (fullAgreement dom (u 0) (u 1) gamma
            (family.q gamma)).card := by
      simpa only [sourceFreshAgreement] using hsplit
    have hfull :
        (fullAgreement dom (u 0) (u 1) gamma
          (family.q gamma)).card = 9 := by
      omega
    have hinter :
        (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          jointCore dom (u 0) (u 1) line.1 line.2).card = 3 := by
      omega
    simp only [regularOutsideLine, Finset.mem_filter]
    exact ⟨hgammaOut, hfresh, hfull, hinter⟩
  have hsmallLe := Finset.card_le_card hsmallSub
  omega

#print axioms card_le_sixteen_of_two_fresh_seven_outsiders
#print axioms outsideLineFreshAtLeast_seven_card_le_one_of_card_gt_sixteen
#print axioms outsideLineAtLeast_ten_card_le_one_of_card_gt_sixteen
#print axioms eight_le_regularOutsideLine_card_of_card_gt_sixteen

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
