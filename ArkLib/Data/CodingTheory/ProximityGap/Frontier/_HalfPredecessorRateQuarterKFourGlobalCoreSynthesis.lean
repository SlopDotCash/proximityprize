/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreSharpSecantExtraction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourLongOutsiderCollapse

/-!
# Rate-quarter `n = 16`, `k = 4`: global core synthesis

This file composes the saturated core-band localization with the complete
overlap-three closure.  Two distinct relevant eight-cores can no longer occur
in a counterexample: intersections of size at most two are covered by the
complementary-core theorem, intersection three is covered by the cubic-locator
theorem, and larger intersections violate the degree-three root cap.

Consequently the global residual splits disjointly into two cases.

* There is a unique relevant eight-core.  Sharp secant extraction supplies a
  distinct core with a five-coordinate petal, exactly three uncovered
  coordinates, and source intersection at most two.  Its size is therefore
  exactly `5`, `6`, or `7`.
* There is no relevant eight-core.  Core-band localization supplies an
  isolated core of size exactly `6` or `7`, and fresh-petal pruning supplies a
  canonical outsider secant with at least three new coordinates.

This is a residual classification, not a proof of the global `|G| <= 16`
bound: both displayed one-reference configurations remain possible in the
current formalized theory.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreSharpSecantExtraction
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourUnequalClosure
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The exact surviving package when a counterexample has a relevant
eight-core.  The source is the unique eight-core, and its sharp extracted
secant has size `5 + overlap`, where the overlap is at most two. -/
structure UniqueEightCoreResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u) where
  source : LineParameter F
  source_mem : source ∈ lineParameters family
  source_core_card :
    (jointCore dom (u 0) (u 1) source.1 source.2).card = 8
  source_unique : ∀ line ∈ lineParameters family,
    8 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card → line = source
  gamma : F
  gamma_outside : gamma ∈ outsideLine family source
  beta : F
  beta_outside : beta ∈ outsideLine family source
  gamma_ne_beta : gamma ≠ beta
  secant_mem : secantParameter family gamma beta ∈ lineParameters family
  secant_ne_source : secantParameter family gamma beta ≠ source
  secant_petal_card : (secantPetal family source gamma beta).card = 5
  uncovered_card :
    (Finset.univ \ (
      jointCore dom (u 0) (u 1) source.1 source.2 ∪
        jointCore dom (u 0) (u 1)
          (secantParameter family gamma beta).1
          (secantParameter family gamma beta).2)).card = 3
  secant_core_card :
    (jointCore dom (u 0) (u 1)
      (secantParameter family gamma beta).1
      (secantParameter family gamma beta).2).card =
      5 +
        (jointCore dom (u 0) (u 1) source.1 source.2 ∩
          jointCore dom (u 0) (u 1)
            (secantParameter family gamma beta).1
            (secantParameter family gamma beta).2).card
  source_secant_inter_card_le_two :
    (jointCore dom (u 0) (u 1) source.1 source.2 ∩
      jointCore dom (u 0) (u 1)
        (secantParameter family gamma beta).1
        (secantParameter family gamma beta).2).card ≤ 2
  eight_regular_outsiders : 8 ≤ (regularOutsideLine family source).card

/-- The exact surviving package when no relevant eight-core exists.  Every
relevant core has size at most seven, and the localized six/seven-core is
isolated from every relevant partner by at least three coordinates. -/
structure NoEightCoreIntermediateResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u) where
  source : LineParameter F
  source_mem : source ∈ lineParameters family
  source_core_card :
    (jointCore dom (u 0) (u 1) source.1 source.2).card = 6 ∨
      (jointCore dom (u 0) (u 1) source.1 source.2).card = 7
  global_core_cap : ∀ line ∈ lineParameters family,
    (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 7
  three_le_uncovered : ∀ line ∈ lineParameters family,
    3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) source line).card
  gamma : F
  gamma_outside : gamma ∈ outsideLine family source
  beta : F
  beta_outside : beta ∈ outsideLine family source
  gamma_ne_beta : gamma ≠ beta
  three_le_secant_petal : 3 ≤ (secantPetal family source gamma beta).card

/-- Distinct relevant decoded lines of degree below four have joint-core
intersection at most three. -/
theorem relevant_jointCore_inter_card_le_three_of_distinct
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {line line' : LineParameter F}
    (hline : line ∈ lineParameters family)
    (hline' : line' ∈ lineParameters family) (hne : line ≠ line') :
    (jointCore dom (u 0) (u 1) line.1 line.2 ∩
      jointCore dom (u 0) (u 1) line'.1 line'.2).card ≤ 3 := by
  have htwo := two_le_pointsOn_card_of_mem_lineParameters family hline
  obtain ⟨gamma, hgamma, beta, hbeta, hgb⟩ := Finset.one_lt_card.mp htwo
  have hnsub : ¬ pointsOn family line ⊆ pointsOn family line' := by
    intro hsub
    have hsec := secantParameter_eq_of_mem_pointsOn family line hgamma hbeta hgb
    have hsec' := secantParameter_eq_of_mem_pointsOn family line'
      (hsub hgamma) (hsub hbeta) hgb
    exact hne (hsec.symm.trans hsec')
  simp only [Finset.not_subset] at hnsub
  obtain ⟨theta, htheta, htheta'⟩ := hnsub
  have hthetaG := pointsOn_subset_G family line htheta
  have hthetaEq := (mem_pointsOn_iff family line theta).mp htheta |>.2
  have hthetaNe : family.q theta ≠ line'.1 + C theta * line'.2 := by
    intro heq
    exact htheta' ((mem_pointsOn_iff family line' theta).mpr ⟨hthetaG, heq⟩)
  have hdeg' := lineParameter_degree_lt family hline'
  have hcap := fullAgreement_inter_jointCore_card_le
    dom (u 0) (u 1) (k := 4) (by norm_num)
      (family.degree_lt theta hthetaG) hdeg'.1 hdeg'.2 hthetaNe
  have hsub :
      jointCore dom (u 0) (u 1) line.1 line.2 ∩
          jointCore dom (u 0) (u 1) line'.1 line'.2 ⊆
        fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
          jointCore dom (u 0) (u 1) line'.1 line'.2 := by
    intro i hi
    rw [Finset.mem_inter] at hi ⊢
    refine ⟨?_, hi.2⟩
    rw [hthetaEq]
    exact jointCore_subset_fullAgreement
      dom (u 0) (u 1) line.1 line.2 theta hi.1
  norm_num at hcap ⊢
  exact (Finset.card_le_card hsub).trans hcap

/-- In a counterexample at `n = 16`, every relevant core has size at most
eight. -/
theorem relevant_core_card_le_eight_of_card_gt_sixteen
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8 := by
  by_contra hnot
  have hn' : Fintype.card I = 2 * 8 := by omega
  have hlarge :
      8 + 4 * (4 - 1) <
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 := by
    omega
  exact largeCore_contradiction_of_card_gt_two_mul
    family (h := 8) (k := 4) (by norm_num) (by norm_num) hn'
      hthreshold hline (by omega) hlarge

/-- **All two-eight-core cases close.**  For distinct relevant eight-cores,
the overlap can only be `0`, `1`, `2`, or `3`; complementary cores close the
first three values and the complete overlap-three theorem closes the last. -/
theorem card_le_sixteen_of_two_distinct_eight_cores
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hne : line1 ≠ line2)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8) :
    family.G.card ≤ 16 := by
  by_cases hcard : family.G.card ≤ 16
  · exact hcard
  have hcard' : 16 < family.G.card := by omega
  have hcap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8 := by
    intro line hline
    exact relevant_core_card_le_eight_of_card_gt_sixteen
      family hn hthreshold hcard' hline
  have hinterCap := relevant_jointCore_inter_card_le_three_of_distinct
    family hline1 hline2 hne
  by_cases hinterSmall :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 2
  · have hn' : Fintype.card I = 2 * 8 := by omega
    have hle := card_le_two_mul_of_saturated_half_cores_inter_le_two
      family (k := 4) (h := 8) (by norm_num) (by norm_num) hn'
        hthreshold line1 line2 hline1 hline2 hcore1 hcore2 hinterSmall
    norm_num at hle ⊢
    exact hle
  · have hinter :
        (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3 := by
      simp only [commonCoreBlock]
      omega
    exact card_le_sixteen_of_overlap_three_core_cap
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hcap

/-- **Global exact residual classification at `n = 16`, `k = 4`.**  Either
the family is domain-bounded, or it has exactly one of the two explicit
one-reference residual packages above. -/
theorem card_le_sixteen_or_unique_eight_core_or_no_eight_intermediate
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨ Nonempty (UniqueEightCoreResidual family) ∨
      Nonempty (NoEightCoreIntermediateResidual family) := by
  by_cases hcard : family.G.card ≤ 16
  · exact Or.inl hcard
  have hcard' : 16 < family.G.card := by omega
  have hn' : Fintype.card I = 2 * 8 := by omega
  have hcap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8 := by
    intro line hline
    exact relevant_core_card_le_eight_of_card_gt_sixteen
      family hn (by omega) hcard' hline
  by_cases hhigh : ∃ line ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  · obtain ⟨line, hline, hcoreLower⟩ := hhigh
    have hcore :
        (jointCore dom (u 0) (u 1) line.1 line.2).card = 8 :=
      Nat.le_antisymm (hcap line hline) hcoreLower
    have hunique : ∀ line2 ∈ lineParameters family,
        8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card →
          line2 = line := by
      intro line2 hline2 hcore2Lower
      have hcore2 :
          (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8 :=
        Nat.le_antisymm (hcap line2 hline2) hcore2Lower
      by_contra hne
      have hle := card_le_sixteen_of_two_distinct_eight_cores
        family hn (by omega) line2 line hline2 hline hne hcore2 hcore
      omega
    rcases card_le_or_second_high_core_or_exact_three_hole_residual
        family (k := 4) (h := 8) (by norm_num) hn' hthreshold
          (by norm_num) hline hcoreLower (by norm_num [hcore]) with
      hle | hsecond | hexact
    · omega
    · obtain ⟨line2, hline2, hlineNe, hcore2⟩ := hsecond
      exact (hlineNe (hunique line2 hline2 hcore2)).elim
    · obtain ⟨gamma, hgamma, beta, hbeta, hne, hline2,
          hlineNe, hpetal, hmissing, hcore2lt, hinter⟩ := hexact
      let line2 := secantParameter family gamma beta
      let D := jointCore dom (u 0) (u 1) line.1 line.2
      let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
      have hpetal' : (secantPetal family line gamma beta).card = 5 := by
        norm_num at hpetal ⊢
        exact hpetal
      have hmissing' :
          (Finset.univ \ (D ∪ D2)).card = 3 := by
        simpa only [D, D2, line2] using hmissing
      have hinter' : (D ∩ D2).card ≤ 2 := by
        norm_num at hinter
        simpa only [D, D2, line2] using hinter
      have hsplit := Finset.card_sdiff_add_card_inter D2 D
      have hpetalEq : secantPetal family line gamma beta = D2 \ D := by
        rfl
      have hD2card : D2.card = 5 + (D ∩ D2).card := by
        rw [hpetalEq] at hpetal'
        rw [Finset.inter_comm] at hsplit
        omega
      have hregular : 8 ≤ (regularOutsideLine family line).card :=
        eight_le_regularOutsideLine_card_of_card_gt_sixteen
          family hn (by omega) hcard' hline hcore
      exact Or.inr (Or.inl ⟨{
        source := line
        source_mem := hline
        source_core_card := hcore
        source_unique := hunique
        gamma := gamma
        gamma_outside := hgamma
        beta := beta
        beta_outside := hbeta
        gamma_ne_beta := hne
        secant_mem := hline2
        secant_ne_source := hlineNe
        secant_petal_card := hpetal'
        uncovered_card := by simpa only [D, D2, line2] using hmissing'
        secant_core_card := by simpa only [D, D2, line2] using hD2card
        source_secant_inter_card_le_two := by
          simpa only [D, D2, line2] using hinter'
        eight_regular_outsiders := hregular }⟩)
  · rcases card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
        family (k := 4) (h := 8) (by norm_num) hn' hthreshold
          (by norm_num) with hle | hhigh' | hmid
    · omega
    · obtain ⟨line, hline, hcore, _⟩ := hhigh'
      exact (hhigh ⟨line, hline, hcore⟩).elim
    · obtain ⟨line, hline, hcoreLower, hcoreLt, _, hisolated⟩ := hmid
      have hcoreCases :
          (jointCore dom (u 0) (u 1) line.1 line.2).card = 6 ∨
            (jointCore dom (u 0) (u 1) line.1 line.2).card = 7 := by
        norm_num at hcoreLower
        omega
      have hglobalCap : ∀ line2 ∈ lineParameters family,
          (jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 7 := by
        intro line2 hline2
        by_contra hnot
        exact hhigh ⟨line2, hline2, by omega⟩
      obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
        exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
          family (k := 4) (h := 8) (by norm_num) hn' hthreshold
            (by norm_num) hcard' hline hcoreLower hcoreLt
      exact Or.inr (Or.inr ⟨{
        source := line
        source_mem := hline
        source_core_card := hcoreCases
        global_core_cap := hglobalCap
        three_le_uncovered := fun line2 hline2 => (hisolated line2 hline2).2
        gamma := gamma
        gamma_outside := hgamma
        beta := beta
        beta_outside := hbeta
        gamma_ne_beta := hne
        three_le_secant_petal := by omega }⟩)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
#print axioms relevant_jointCore_inter_card_le_three_of_distinct
#print axioms relevant_core_card_le_eight_of_card_gt_sixteen
#print axioms card_le_sixteen_of_two_distinct_eight_cores
#print axioms card_le_sixteen_or_unique_eight_core_or_no_eight_intermediate
