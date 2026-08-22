/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo

/-!
# Rate-quarter `k = 4`: consume the forced cross-triple secant

The cross-triple unique-core consumer produces a canonical six- or seven-core
secant.  This file makes that secant the distinguished line of a fresh
`UniqueEightCoreResidual` whenever it leaves three holes.  The affine-plane
population theorem then gives four or five regular outsiders off both lines.

Exactly one alternative remains outside that consumer: a six-core meeting the
source core in two coordinates and leaving four holes.  In that cell every
selected point off both lines agrees on at least three of the four holes.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Any threshold-nine selected point off two relevant lines agrees on at
least three coordinates outside their core union. -/
theorem three_le_uncoveredAgreement_of_off_both
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    {theta : F} (htheta : theta ∈ family.G)
    (hoff1 : family.q theta ≠ line1.1 + C theta * line1.2)
    (hoff2 : family.q theta ≠ line2.1 + C theta * line2.2) :
    3 ≤ (fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2))).card := by
  let Full := fullAgreement dom (u 0) (u 1) theta (family.q theta)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let H := Finset.univ \ (D1 ∪ D2)
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  have hcap1 : (Full ∩ D1).card ≤ 3 := by
    have hcap := fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) (k := 4) (by norm_num)
        (family.degree_lt theta htheta) hdeg1.1 hdeg1.2 hoff1
    norm_num at hcap
    simpa only [Full, D1] using hcap
  have hcap2 : (Full ∩ D2).card ≤ 3 := by
    have hcap := fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) (k := 4) (by norm_num)
        (family.degree_lt theta htheta) hdeg2.1 hdeg2.2 hoff2
    norm_num at hcap
    simpa only [Full, D2] using hcap
  have hcover : Full ⊆ ((Full ∩ D1) ∪ (Full ∩ D2)) ∪ (Full ∩ H) := by
    intro i hi
    by_cases hi1 : i ∈ D1
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hi1⟩))
    by_cases hi2 : i ∈ D2
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hi, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, fun hiUnion =>
            (Finset.mem_union.mp hiUnion).elim hi1 hi2⟩⟩)
  have hupper : Full.card ≤
      (Full ∩ D1).card + (Full ∩ D2).card + (Full ∩ H).card := by
    calc
      Full.card ≤ (((Full ∩ D1) ∪ (Full ∩ D2)) ∪ (Full ∩ H)).card :=
        Finset.card_le_card hcover
      _ ≤ ((Full ∩ D1) ∪ (Full ∩ D2)).card + (Full ∩ H).card :=
        Finset.card_union_le _ _
      _ ≤ ((Full ∩ D1).card + (Full ∩ D2).card) + (Full ∩ H).card := by
        gcongr
        exact Finset.card_union_le _ _
  have hlower : 9 ≤ Full.card :=
    hthreshold.trans (family.threshold_le theta htheta)
  change 3 ≤ (Full ∩ H).card
  omega

/-- Repackage a three-hole cross-triple secant as the distinguished secant of
a `UniqueEightCoreResidual`. -/
noncomputable def threeHoleCrossResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (hholes :
      (Finset.univ \ (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2 ∪
          jointCore dom (u 0) (u 1)
            (secantParameter family cross.gamma1 cross.gamma2).1
            (secantParameter family cross.gamma1 cross.gamma2).2)).card = 3) :
    UniqueEightCoreResidual family where
  source := residual.source
  source_mem := residual.source_mem
  source_core_card := residual.source_core_card
  source_unique := residual.source_unique
  gamma := cross.gamma1
  gamma_outside := by
    have h := cross.gamma1_regular
    simp only [regularOutsideLine, Finset.mem_filter] at h
    exact h.1
  beta := cross.gamma2
  beta_outside := by
    have h := cross.gamma2_regular
    simp only [regularOutsideLine, Finset.mem_filter] at h
    exact h.1
  gamma_ne_beta := cross.gamma12
  secant_mem := cross.secant_mem
  secant_ne_source := cross.secant_ne_source
  secant_petal_card := by
    let D := jointCore dom (u 0) (u 1)
      residual.source.1 residual.source.2
    let D2 := jointCore dom (u 0) (u 1)
      (secantParameter family cross.gamma1 cross.gamma2).1
      (secantParameter family cross.gamma1 cross.gamma2).2
    have hbalance : 3 + D2.card = 8 + (D ∩ D2).card := by
      rw [← hholes]
      simpa only [D, D2] using cross.uncovered_balance
    have hsplit := Finset.card_sdiff_add_card_inter D2 D
    have hpetal : (D2 \ D).card = 5 := by
      rw [Finset.inter_comm] at hsplit
      omega
    simpa only [secantPetal, D, D2] using hpetal
  uncovered_card := hholes
  secant_core_card := by
    let D := jointCore dom (u 0) (u 1)
      residual.source.1 residual.source.2
    let D2 := jointCore dom (u 0) (u 1)
      (secantParameter family cross.gamma1 cross.gamma2).1
      (secantParameter family cross.gamma1 cross.gamma2).2
    have hbalance : 3 + D2.card = 8 + (D ∩ D2).card := by
      rw [← hholes]
      simpa only [D, D2] using cross.uncovered_balance
    change D2.card = 5 + (D ∩ D2).card
    omega
  source_secant_inter_card_le_two := cross.source_secant_inter_card_le_two
  eight_regular_outsiders := residual.eight_regular_outsiders

/-- **Forced-cross composition.**  The core-six/overlap-one and
core-seven/overlap-two alternatives produce a new three-hole residual whose
off-secant regular population is four or five.  The only remaining branch is
the core-six/overlap-two four-hole cell, where every off-both selected point
uses at least three holes. -/
theorem crossTriple_threeHole_population_or_fourHole
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) :
    (∃ residual2 : UniqueEightCoreResidual family,
      residual2.source = residual.source ∧
      residual2.gamma = cross.gamma1 ∧ residual2.beta = cross.gamma2 ∧
      4 ≤ (regularOffResidualSecant family residual2).card ∧
        (regularOffResidualSecant family residual2).card ≤ 5) ∨
    ((jointCore dom (u 0) (u 1)
        (secantParameter family cross.gamma1 cross.gamma2).1
        (secantParameter family cross.gamma1 cross.gamma2).2).card = 6 ∧
      (jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1)
          (secantParameter family cross.gamma1 cross.gamma2).1
          (secantParameter family cross.gamma1 cross.gamma2).2).card = 2 ∧
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
          jointCore dom (u 0) (u 1)
            (secantParameter family cross.gamma1 cross.gamma2).1
            (secantParameter family cross.gamma1 cross.gamma2).2)).card = 4 ∧
      ∀ theta ∈ family.G,
        family.q theta ≠ residual.source.1 + C theta * residual.source.2 →
        family.q theta ≠
          (secantParameter family cross.gamma1 cross.gamma2).1 +
            C theta * (secantParameter family cross.gamma1 cross.gamma2).2 →
        3 ≤ (fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
          (Finset.univ \ (
            jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
              jointCore dom (u 0) (u 1)
                (secantParameter family cross.gamma1 cross.gamma2).1
                (secantParameter family cross.gamma1 cross.gamma2).2))).card) := by
  let line2 := secantParameter family cross.gamma1 cross.gamma2
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let H := Finset.univ \ (D ∪ D2)
  have hline2 : line2 ∈ lineParameters family := by
    simpa only [line2] using cross.secant_mem
  have favorable (hholes : H.card = 3) :
      ∃ residual2 : UniqueEightCoreResidual family,
        residual2.source = residual.source ∧
        residual2.gamma = cross.gamma1 ∧ residual2.beta = cross.gamma2 ∧
        4 ≤ (regularOffResidualSecant family residual2).card ∧
          (regularOffResidualSecant family residual2).card ≤ 5 := by
    let residual2 := threeHoleCrossResidual residual cross (by
      simpa only [H, D, D2, line2] using hholes)
    have hsix : 6 ≤
        (jointCore dom (u 0) (u 1)
          (residualSecantLine residual2).1
          (residualSecantLine residual2).2).card := by
      rcases cross.secant_core_card with hcore | hcore
      · simpa only [residual2, threeHoleCrossResidual,
          residualSecantLine] using (show 6 ≤ D2.card by
            simpa only [D2, line2] using hcore.ge)
      · simpa only [residual2, threeHoleCrossResidual,
          residualSecantLine] using (show 6 ≤ D2.card by
            have : D2.card = 7 := by simpa only [D2, line2] using hcore
            omega)
    have hrange :=
      regularOffResidualSecant_card_four_five_of_six_le_secant_core
        family hn hthreshold residual2 hsix
    exact ⟨residual2, rfl, rfl, rfl, hrange⟩
  rcases cross.secant_core_card with hcore6 | hcore7
  · rcases cross.core_six_data hcore6 with hthree | hfour
    · exact Or.inl (favorable (by
        simpa only [H, D, D2, line2] using hthree.2))
    · apply Or.inr
      refine ⟨hcore6, hfour.1, hfour.2, ?_⟩
      intro theta htheta hoff1 hoff2
      exact three_le_uncoveredAgreement_of_off_both
        family hthreshold.ge residual.source line2
          residual.source_mem hline2 htheta hoff1 hoff2
  · have hthree := cross.core_seven_data hcore7
    exact Or.inl (favorable (by
      simpa only [H, D, D2, line2] using hthree.2))

#print axioms three_le_uncoveredAgreement_of_off_both
#print axioms threeHoleCrossResidual
#print axioms crossTriple_threeHole_population_or_fourHole

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer
