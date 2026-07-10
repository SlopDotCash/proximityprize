/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourPopulation

/-!
# The final unequal-slope residual in the `n = 16`, `k = 4` overlap-three cell

The common cubic factor controls points on the two reference lines as well as
points off both lines.  A selected point lying on exactly one reference line
cannot use a fresh agreement coordinate in the other line's five-coordinate
petal: evaluation of the common-factor identity at such a coordinate would
force the two polynomial pencils to meet at that scalar, putting the point on
both lines.  Thus exclusive points on either line inject into the
three-coordinate complement of the two cores.

Each exclusive part consequently has size at most three.  The two reference
lines meet in at most one selected scalar, so their union has size at most
seven.  Together with the ten-point off-both matching bound this gives
`|G| <= 17`.  If `|G| > 16`, every constituent bound is forced to equality:
there are three exclusive points on each line, one common point, and ten
off-both points.  The equal-slope closure then forces the reference slopes to
be unequal.  This isolates the exact remaining one-point residual.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A fresh agreement of a point exclusive to the first reference line lies
outside both reference cores.  The common cubic factor is what excludes the
second core's petal. -/
theorem exclusive_first_freshAgreement_subset_coreUnion_complement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    {gamma : F}
    (hgamma : gamma ∈ pointsOn family line1 \ pointsOn family line2) :
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
        jointCore dom (u 0) (u 1) line1.1 line1.2 ⊆
      Finset.univ \
        (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2) := by
  obtain ⟨_qa, _qr, alpha, rho, _hqa0, _hqr0, _hqaC, _hqrC,
      _hfactorA0, _hfactorR0, hfactorA, hfactorR, _hproportional,
      _hcommonDeg⟩ :=
    decoded_line_differences_kfour_common_factor
      family line1 line2 hline1 hline2 hinter
  have hgamma' := Finset.mem_sdiff.mp hgamma
  have hgammaOn1 := (mem_pointsOn_iff family line1 gamma).mp hgamma'.1
  have hgammaNotOn2 : gamma ∉ pointsOn family line2 := hgamma'.2
  intro i hi
  have hiFresh := Finset.mem_sdiff.mp hi
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  intro hiUnion
  rcases Finset.mem_union.mp hiUnion with hiCore1 | hiCore2
  · exact hiFresh.2 hiCore1
  · have hiNotCommon :
        i ∉ commonCoreBlock dom (u 0) (u 1) line1 line2 := by
      intro hiCommon
      exact hiFresh.2 (Finset.inter_subset_left hiCommon)
    have hlocatorEval :
        (domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2)).eval (dom i) ≠ 0 := by
      rw [ne_eq,
        eval_domainRootProduct_eq_zero_iff_mem dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) i]
      exact hiNotCommon
    have hiAgreeLine1 : i ∈ fullAgreement dom (u 0) (u 1) gamma
        (line1.1 + C gamma * line1.2) := by
      simpa only [hgammaOn1.2] using hiFresh.1
    have hequation :
        (line1.1 - line2.1).eval (dom i) +
          gamma * (line1.2 - line2.2).eval (dom i) = 0 := by
      simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
        true_and, eval_add, eval_mul, eval_C] at hiAgreeLine1
      simp only [jointCore, Finset.mem_filter, Finset.mem_univ,
        true_and] at hiCore2
      simp only [eval_sub]
      linear_combination hiAgreeLine1 - hiCore2.1 - gamma * hiCore2.2
    have hequation' :
        line1.1.eval (dom i) - line2.1.eval (dom i) +
          gamma * (line1.2.eval (dom i) - line2.2.eval (dom i)) = 0 := by
      simpa only [eval_sub] using hequation
    have hfactorPencil :
        (line2.1 - line1.1) + C gamma * (line2.2 - line1.2) =
          C (alpha + gamma * rho) *
            domainRootProduct dom
              (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
      rw [hfactorA, hfactorR, C_add, C_mul]
      ring
    have hevalFactor :
        (alpha + gamma * rho) *
            (domainRootProduct dom
              (commonCoreBlock dom (u 0) (u 1) line1 line2)).eval (dom i) = 0 := by
      have hevalPencil :
          ((line2.1 - line1.1) + C gamma *
            (line2.2 - line1.2)).eval (dom i) = 0 := by
        simp only [eval_add, eval_mul, eval_C, eval_sub]
        calc
          line2.1.eval (dom i) - line1.1.eval (dom i) +
                gamma * (line2.2.eval (dom i) - line1.2.eval (dom i)) =
              -((line1.1.eval (dom i) - line2.1.eval (dom i)) +
                gamma * (line1.2.eval (dom i) - line2.2.eval (dom i))) := by
            ring
          _ = 0 := neg_eq_zero.mpr hequation'
      rw [hfactorPencil, eval_mul, eval_C] at hevalPencil
      exact hevalPencil
    have hscalar : alpha + gamma * rho = 0 :=
      (mul_eq_zero.mp hevalFactor).resolve_right hlocatorEval
    have hpencilsEqual :
        line1.1 + C gamma * line1.2 =
          line2.1 + C gamma * line2.2 := by
      apply sub_eq_zero.mp
      calc
        (line1.1 + C gamma * line1.2) -
            (line2.1 + C gamma * line2.2) =
          -((line2.1 - line1.1) + C gamma *
            (line2.2 - line1.2)) := by ring
        _ = -(C (alpha + gamma * rho) *
            domainRootProduct dom
              (commonCoreBlock dom (u 0) (u 1) line1 line2)) := by
          rw [hfactorPencil]
        _ = 0 := by rw [hscalar]; simp
    apply hgammaNotOn2
    rw [mem_pointsOn_iff]
    exact ⟨hgammaOn1.1, hgammaOn1.2.trans hpencilsEqual⟩

/-- At most three selected points lie on the first reference line but not the
second. -/
theorem exclusive_first_pointsOn_card_le_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    (pointsOn family line1 \ pointsOn family line2).card ≤ 3 := by
  let E := pointsOn family line1 \ pointsOn family line2
  let R := Finset.univ \
    (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
      jointCore dom (u 0) (u 1) line2.1 line2.2)
  have hinter' :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
    simpa only [commonCoreBlock] using hinter
  have hRcard : R.card = 3 := by
    have hunionInter := Finset.card_union_add_card_inter
      (jointCore dom (u 0) (u 1) line1.1 line1.2)
      (jointCore dom (u 0) (u 1) line2.1 line2.2)
    have hcomplement : R.card = Fintype.card I -
        (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
      simp only [R, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ]
    omega
  have hdeg1 := lineParameter_degree_lt family hline1
  have hfresh : ∀ gamma : {gamma // gamma ∈ E},
      ∃ i, i ∈ fullAgreement dom (u 0) (u 1) gamma.1
          (family.q gamma.1) \
        jointCore dom (u 0) (u 1) line1.1 line1.2 := by
    intro gamma
    have hgammaE : gamma.1 ∈
        pointsOn family line1 \ pointsOn family line2 := by
      simpa only [E] using gamma.2
    have hgammaG :=
      (mem_pointsOn_iff family line1 gamma.1).mp
        (Finset.mem_sdiff.mp hgammaE).1 |>.1
    exact Finset.sdiff_nonempty.mpr <|
      not_subset_jointCore_of_not_pairJointAgreesOn
        dom (u 0) (u 1)
          (fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1))
          line1.1 line1.2 hdeg1.1 hdeg1.2
          (family.noJoint gamma.1 hgammaG)
  choose coord hcoord using hfresh
  have hcoordR : ∀ gamma : {gamma // gamma ∈ E}, coord gamma ∈ R := by
    intro gamma
    have hgammaE : gamma.1 ∈
        pointsOn family line1 \ pointsOn family line2 := by
      simpa only [E] using gamma.2
    have hsub := exclusive_first_freshAgreement_subset_coreUnion_complement
      family line1 line2 hline1 hline2 hinter hgammaE
    simpa only [R] using hsub (hcoord gamma)
  let f : {gamma // gamma ∈ E} → {i // i ∈ R} := fun gamma =>
    ⟨coord gamma, hcoordR gamma⟩
  have hf : Function.Injective f := by
    intro gamma beta heq
    apply Subtype.ext
    by_contra hne
    have hcoordEq : coord gamma = coord beta := congrArg Subtype.val heq
    have hgammaE : gamma.1 ∈
        pointsOn family line1 \ pointsOn family line2 := by
      simpa only [E] using gamma.2
    have hbetaE : beta.1 ∈
        pointsOn family line1 \ pointsOn family line2 := by
      simpa only [E] using beta.2
    have hgammaLine :=
      (mem_pointsOn_iff family line1 gamma.1).mp
        (Finset.mem_sdiff.mp hgammaE).1 |>.2
    have hbetaLine :=
      (mem_pointsOn_iff family line1 beta.1).mp
        (Finset.mem_sdiff.mp hbetaE).1 |>.2
    have hgammaFresh := hcoord gamma
    have hbetaFresh := hcoord beta
    rw [hgammaLine] at hgammaFresh
    rw [hbetaLine] at hbetaFresh
    have hbetaAtGamma : coord gamma ∈
        fullAgreement dom (u 0) (u 1) beta.1
            (line1.1 + C beta.1 * line1.2) \
          jointCore dom (u 0) (u 1) line1.1 line1.2 := by
      rw [hcoordEq]
      exact hbetaFresh
    exact (Finset.disjoint_left.mp
      (freshAgreement_disjoint dom (u 0) (u 1)
        line1.1 line1.2 hne)) hgammaFresh hbetaAtGamma
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, E, hRcard] using hcard

/-- The symmetric exclusive-line bound. -/
theorem exclusive_second_pointsOn_card_le_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    (pointsOn family line2 \ pointsOn family line1).card ≤ 3 := by
  have hinterSymm :
      (commonCoreBlock dom (u 0) (u 1) line2 line1).card = 3 := by
    simpa only [commonCoreBlock, Finset.inter_comm] using hinter
  exact exclusive_first_pointsOn_card_le_three
    family hn line2 line1 hline2 hline1 hcore2 hcore1 hinterSymm

/-- The two distinct overlap-three reference lines share at most one selected
scalar. -/
theorem reference_pointsOn_inter_card_le_one
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    (pointsOn family line1 ∩ pointsOn family line2).card ≤ 1 := by
  obtain ⟨_qa, _qr, alpha, rho, _hqa0, _hqr0, _hqaC, _hqrC,
      _hfactorA0, _hfactorR0, hfactorA, hfactorR, _hproportional,
      _hcommonDeg⟩ :=
    decoded_line_differences_kfour_common_factor
      family line1 line2 hline1 hline2 hinter
  let P := domainRootProduct dom
    (commonCoreBlock dom (u 0) (u 1) line1 line2)
  have hP : P ≠ 0 :=
    (domainRootProduct_monic dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2)).ne_zero
  have hlineNe : line1 ≠ line2 := by
    intro heq
    subst line2
    simp only [commonCoreBlock, Finset.inter_self] at hinter
    omega
  have hcoeff : alpha ≠ 0 ∨ rho ≠ 0 :=
    coefficient_pair_nonzero_of_distinct P alpha rho line1 line2
      (by simpa only [P] using hfactorA)
      (by simpa only [P] using hfactorR) hlineNe
  have hunique := unique_line_intersection_of_common_factor
    P hP alpha rho line1 line2
      (by simpa only [P] using hfactorA)
      (by simpa only [P] using hfactorR) hcoeff
  rw [Finset.card_le_one]
  intro gamma hgamma beta hbeta
  have hgamma' := Finset.mem_inter.mp hgamma
  have hbeta' := Finset.mem_inter.mp hbeta
  have hgamma1 := (mem_pointsOn_iff family line1 gamma).mp hgamma'.1
  have hgamma2 := (mem_pointsOn_iff family line2 gamma).mp hgamma'.2
  have hbeta1 := (mem_pointsOn_iff family line1 beta).mp hbeta'.1
  have hbeta2 := (mem_pointsOn_iff family line2 beta).mp hbeta'.2
  apply hunique gamma beta
  · exact hgamma1.2.symm.trans hgamma2.2
  · exact hbeta1.2.symm.trans hbeta2.2

/-- The union of the two overlap-three reference lines contains at most seven
selected scalars. -/
theorem reference_pointsOn_union_card_le_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    (pointsOn family line1 ∪ pointsOn family line2).card ≤ 7 := by
  have hfirst := exclusive_first_pointsOn_card_le_three
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hsecond := exclusive_second_pointsOn_card_le_three
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hinterCard := reference_pointsOn_inter_card_le_one
    family line1 line2 hline1 hline2 hcore1 hinter
  have hsplit1 := Finset.card_sdiff_add_card_inter
    (pointsOn family line1) (pointsOn family line2)
  have hsplit2 := Finset.card_sdiff_add_card_inter
    (pointsOn family line2) (pointsOn family line1)
  have hunion := Finset.card_union_add_card_inter
    (pointsOn family line1) (pointsOn family line2)
  have hinterSymm :
      (pointsOn family line2 ∩ pointsOn family line1).card =
        (pointsOn family line1 ∩ pointsOn family line2).card := by
    rw [Finset.inter_comm]
  omega

/-- Combining the seven points on the reference lines with the ten-point
off-both matching bound leaves a single point above the desired sixteen. -/
theorem card_le_seventeen_of_overlap_three_core_cap
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
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    family.G.card ≤ 17 := by
  have hlines := reference_pointsOn_union_card_le_seven
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hoff := offBothPoints_card_le_ten_of_relevant_core_cap
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hcoreCap
  have hcover : family.G ⊆
      (pointsOn family line1 ∪ pointsOn family line2) ∪
        offBothPoints family line1 line2 := by
    intro gamma hgamma
    by_cases hfirst :
        family.q gamma = line1.1 + C gamma * line1.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, hfirst⟩))
    by_cases hsecond :
        family.q gamma = line2.1 + C gamma * line2.2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, hsecond⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hgamma, hfirst, hsecond⟩)
  have hcoverCard := Finset.card_le_card hcover
  have hall := Finset.card_union_le
    (pointsOn family line1 ∪ pointsOn family line2)
    (offBothPoints family line1 line2)
  omega

/-- **Exact one-point residual.**  If the target `|G| <= 16` fails, then all
line and off-line bounds saturate and the two reference slopes are unequal. -/
theorem overlap_three_core_cap_saturation_of_sixteen_lt_card
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
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8)
    (hcard : 16 < family.G.card) :
    family.G.card = 17 ∧
      (offBothPoints family line1 line2).card = 10 ∧
      (pointsOn family line1 \ pointsOn family line2).card = 3 ∧
      (pointsOn family line2 \ pointsOn family line1).card = 3 ∧
      (pointsOn family line1 ∩ pointsOn family line2).card = 1 ∧
      line2.2 ≠ line1.2 := by
  have hfirst := exclusive_first_pointsOn_card_le_three
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hsecond := exclusive_second_pointsOn_card_le_three
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hinterCard := reference_pointsOn_inter_card_le_one
    family line1 line2 hline1 hline2 hcore1 hinter
  have hlines := reference_pointsOn_union_card_le_seven
    family hn line1 line2 hline1 hline2 hcore1 hcore2 hinter
  have hoff := offBothPoints_card_le_ten_of_relevant_core_cap
    family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
      hinter hcoreCap
  have hcover : family.G ⊆
      (pointsOn family line1 ∪ pointsOn family line2) ∪
        offBothPoints family line1 line2 := by
    intro gamma hgamma
    by_cases hfirstEq :
        family.q gamma = line1.1 + C gamma * line1.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, hfirstEq⟩))
    by_cases hsecondEq :
        family.q gamma = line2.1 + C gamma * line2.2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, hsecondEq⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hgamma, hfirstEq, hsecondEq⟩)
  have hcoverCard := Finset.card_le_card hcover
  have hall := Finset.card_union_le
    (pointsOn family line1 ∪ pointsOn family line2)
    (offBothPoints family line1 line2)
  have hsplit1 := Finset.card_sdiff_add_card_inter
    (pointsOn family line1) (pointsOn family line2)
  have hsplit2 := Finset.card_sdiff_add_card_inter
    (pointsOn family line2) (pointsOn family line1)
  have hunion := Finset.card_union_add_card_inter
    (pointsOn family line1) (pointsOn family line2)
  have hinterSymm :
      (pointsOn family line2 ∩ pointsOn family line1).card =
        (pointsOn family line1 ∩ pointsOn family line2).card := by
    rw [Finset.inter_comm]
  have hslopes : line2.2 ≠ line1.2 := by
    intro hslope
    have hle := card_le_sixteen_of_equal_slope_overlap_three_core_cap
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hslope hcoreCap
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, hslopes⟩ <;> omega

#print axioms exclusive_first_freshAgreement_subset_coreUnion_complement
#print axioms exclusive_first_pointsOn_card_le_three
#print axioms reference_pointsOn_inter_card_le_one
#print axioms reference_pointsOn_union_card_le_seven
#print axioms card_le_seventeen_of_overlap_three_core_cap
#print axioms overlap_three_core_cap_saturation_of_sixteen_lt_card

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalResidual
