/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSignatures
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirectionConsumer

/-!
# Shared holes versus primitive injection in the unique-core residual

In the `n = 16`, `k = 4` unique-eight-core residual, at least four regular
outsiders lie off the distinguished sub-high secant.  The exact signature
theorem says that the same three residual holes lie in the secant core of
every pair of these outsiders.

This has two opposite consequences for primitive injection.

* The holes cannot themselves be used as primitive fresh coordinates: they
  already lie in every pair-source core.
* A regular outsider has nine agreements while every off-secant pair core has
  size at most seven.  It therefore has at least two agreements outside that
  pair-source core, and none of them can be trapped in the shared holes.

Thus a regular outsider which is hole-trapped relative to a pair secant
through another off-secant regular outsider must lie on the distinguished
secant.  For four off-secant outsiders every member admits a partner for which
the pair-source hole trap fails.  This removes the hole-trapping alternative
for these pair sources, but it does not supply a common determinant-collapsed
target assignment, so it is not a closure of the unique-core branch.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirectionConsumer

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSharedHolePrimitive

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The three coordinates missed by the unique eight-core and its
distinguished sub-high secant. -/
noncomputable def residualHoles
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) : Finset I :=
  Finset.univ \ (
    jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2 ∪
      jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2)

/-- The residual hole set has exactly three coordinates. -/
theorem residualHoles_card
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) :
    (residualHoles residual).card = 3 := by
  simpa only [residualHoles, residualSecantLine] using
    residual.uncovered_card

/-- The secant core of two off-secant regular outsiders is contained in the
full agreement set of either endpoint. -/
theorem pair_secant_core_subset_fullAgreement_left
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (phi : F) {theta : F}
    (htheta : theta ∈ regularOutsideLine family residual.source) :
    jointCore dom (u 0) (u 1)
        (secantParameter family theta phi).1
        (secantParameter family theta phi).2 ⊆
      fullAgreement dom (u 0) (u 1) theta (family.q theta) := by
  have hthetaData := htheta
  simp only [regularOutsideLine, Finset.mem_filter] at hthetaData
  have hthetaG :=
    (mem_outsideLine_iff family residual.source theta).mp
      hthetaData.1 |>.1
  have hthetaOn : theta ∈
      pointsOn family (secantParameter family theta phi) :=
    first_point_mem_pointsOn_secant family hthetaG
  have hthetaEq :=
    (mem_pointsOn_iff family (secantParameter family theta phi) theta).mp
      hthetaOn |>.2
  simpa only [hthetaEq] using
    (jointCore_subset_fullAgreement dom (u 0) (u 1)
      (secantParameter family theta phi).1
      (secantParameter family theta phi).2 theta)

/-- An off-secant regular outsider has at least two agreements outside the
core of every pair secant through another off-secant regular outsider. -/
theorem two_le_pair_source_outsideAgreements
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi) :
    2 ≤ (outsideSourceAgreements family theta
      (secantParameter family theta phi)).card := by
  have hthetaData := htheta
  have hphiData := hphi
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData hphiData
  have hthetaRegular := hthetaData.1
  have hphiRegular := hphiData.1
  have hthetaRegularData := hthetaRegular
  simp only [regularOutsideLine, Finset.mem_filter] at hthetaRegularData
  have hfull :
      (fullAgreement dom (u 0) (u 1) theta
        (family.q theta)).card = 9 := hthetaRegularData.2.2.1
  have hcoreUpper :=
    (offResidualSecant_pair_core_band
      family hn residual htheta hphi hne).2
  have hcoreSubset := pair_secant_core_subset_fullAgreement_left
    family residual phi hthetaRegular
  rw [outsideSourceAgreements,
    Finset.card_sdiff_of_subset hcoreSubset]
  omega

/-- The common residual holes are unusable as fresh coordinates relative to
an off-secant pair source: all three already lie in that pair core. -/
theorem residualHoles_disjoint_pair_source_outsideAgreements
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi) :
    Disjoint (residualHoles residual)
      (outsideSourceAgreements family theta
        (secantParameter family theta phi)) := by
  have hholesCore : residualHoles residual ⊆
      jointCore dom (u 0) (u 1)
        (secantParameter family theta phi).1
        (secantParameter family theta phi).2 := by
    simpa only [residualHoles] using
      residual_holes_subset_pair_secant_core
        family hn residual htheta hphi hne
  apply Finset.disjoint_left.mpr
  intro i hiHole hiOutside
  have hiNotCore : i ∉ jointCore dom (u 0) (u 1)
      (secantParameter family theta phi).1
      (secantParameter family theta phi).2 := by
    exact (Finset.mem_sdiff.mp hiOutside).2
  exact hiNotCore (hholesCore hiHole)

/-- **Off-secant pair sources cannot be hole-trapped.**  They have at least
two outside-source agreements, while the shared holes lie inside the source
core and hence contain none of those agreements. -/
theorem not_pair_source_hole_trapped_of_regularOff
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi) :
    ¬ outsideSourceAgreements family theta
        (secantParameter family theta phi) ⊆ residualHoles residual := by
  intro htrapped
  have htwo := two_le_pair_source_outsideAgreements
    family hn residual htheta hphi hne
  have hpos : 0 < (outsideSourceAgreements family theta
      (secantParameter family theta phi)).card := by omega
  obtain ⟨i, hiOutside⟩ := Finset.card_pos.mp hpos
  have hdisjoint := Finset.disjoint_left.mp
    (residualHoles_disjoint_pair_source_outsideAgreements
      family hn residual htheta hphi hne)
  exact hdisjoint (htrapped hiOutside) hiOutside

/-- **Hole trap forces the distinguished secant.**  Let `theta` be any
regular outsider and `phi` an off-distinguished-secant regular outsider.  If
the agreements of `theta` outside their pair-secant core are all residual
holes, then `theta` lies on the distinguished secant. -/
theorem mem_residualSecant_of_regular_hole_trapped_pair_source
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta phi : F}
    (htheta : theta ∈ regularOutsideLine family residual.source)
    (hphi : phi ∈ regularOffResidualSecant family residual)
    (hne : theta ≠ phi)
    (htrapped : outsideSourceAgreements family theta
      (secantParameter family theta phi) ⊆ residualHoles residual) :
    theta ∈ pointsOn family (residualSecantLine residual) := by
  by_contra hnotOn
  have hthetaOff : theta ∈ regularOffResidualSecant family residual :=
    Finset.mem_sdiff.mpr ⟨htheta, hnotOn⟩
  exact (not_pair_source_hole_trapped_of_regularOff
    family hn residual hthetaOff hphi hne) htrapped

/-- **Four shared-hole outsiders all escape pair-source trapping.**  From any
four off-secant regular outsiders, every chosen outsider has another chosen
partner whose pair core contains the common holes, but whose outside-source
agreement set has size at least two and is not contained in those holes.

This is the exact remaining handoff to a future primitive assignment: one
still has to place these escaping coordinates into target cores belonging to
one common determinant-collapsed cluster. -/
theorem exists_four_regular_pair_source_hole_escapes
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    (hfour : 4 ≤ (regularOffResidualSecant family residual).card) :
    ∃ S : Finset F,
      S ⊆ regularOffResidualSecant family residual ∧ S.card = 4 ∧
        ∀ theta ∈ S, ∃ phi ∈ S, theta ≠ phi ∧
          residualHoles residual ⊆
            jointCore dom (u 0) (u 1)
              (secantParameter family theta phi).1
              (secantParameter family theta phi).2 ∧
          2 ≤ (outsideSourceAgreements family theta
            (secantParameter family theta phi)).card ∧
          ¬ outsideSourceAgreements family theta
              (secantParameter family theta phi) ⊆ residualHoles residual := by
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hfour
  refine ⟨S, hSsub, hScard, ?_⟩
  intro theta hthetaS
  have hSlarge : 1 < S.card := by omega
  obtain ⟨phi, hphiS, hphiTheta⟩ :=
    Finset.exists_mem_ne hSlarge theta
  have hne : theta ≠ phi := hphiTheta.symm
  have htheta := hSsub hthetaS
  have hphi := hSsub hphiS
  refine ⟨phi, hphiS, hne, ?_, ?_, ?_⟩
  · simpa only [residualHoles] using
      residual_holes_subset_pair_secant_core
        family hn residual htheta hphi hne
  · exact two_le_pair_source_outsideAgreements
      family hn residual htheta hphi hne
  · exact not_pair_source_hole_trapped_of_regularOff
      family hn residual htheta hphi hne

/-- The unique-core residual supplies the four-element escape configuration
unconditionally: its existing population theorem provides the required four
off-secant regular outsiders. -/
theorem residual_exists_four_regular_pair_source_hole_escapes
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family) :
    ∃ S : Finset F,
      S ⊆ regularOffResidualSecant family residual ∧ S.card = 4 ∧
        ∀ theta ∈ S, ∃ phi ∈ S, theta ≠ phi ∧
          residualHoles residual ⊆
            jointCore dom (u 0) (u 1)
              (secantParameter family theta phi).1
              (secantParameter family theta phi).2 ∧
          2 ≤ (outsideSourceAgreements family theta
            (secantParameter family theta phi)).card ∧
          ¬ outsideSourceAgreements family theta
              (secantParameter family theta phi) ⊆ residualHoles residual := by
  apply exists_four_regular_pair_source_hole_escapes family hn residual
  exact four_le_regularOffResidualSecant_card
    family hn hthreshold residual

#print axioms residualHoles_card
#print axioms pair_secant_core_subset_fullAgreement_left
#print axioms two_le_pair_source_outsideAgreements
#print axioms residualHoles_disjoint_pair_source_outsideAgreements
#print axioms not_pair_source_hole_trapped_of_regularOff
#print axioms mem_residualSecant_of_regular_hole_trapped_pair_source
#print axioms exists_four_regular_pair_source_hole_escapes
#print axioms residual_exists_four_regular_pair_source_hole_escapes

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSharedHolePrimitive
