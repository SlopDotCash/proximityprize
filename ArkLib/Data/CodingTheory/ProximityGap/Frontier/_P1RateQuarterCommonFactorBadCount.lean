/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedSafeEvents
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedUnsafeEvents
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterBadLabelFamilyConnector

/-!
# Operational bad-label count for the saturated P1 common-factor amplifier

The saturated construction supplies one safe label at every coordinate outside the common roots
and isolated holes, and three unsafe labels at every isolated hole.  This module proves those
labels are all distinct, counts the family as exactly `N+2`, embeds it in the literal bad-event
filter, and feeds it to the operational MCA upper ledger.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorBadCount

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorConstruction
open P1RateQuarterSaturatedConstruction
open P1RateQuarterBadLabelFamilyConnector

local instance localInstance_P1RateQuarterCommonFactorBadCount_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

abbrev certificateCode : Set (Coord → F) :=
  ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))

/-! ## Structural safe-coordinate count -/

noncomputable def saturatedSafeCoords : Finset Coord :=
  ((Finset.univ : Finset Coord) \ (commonRoots ∪ newHoles)).erase hole

abbrev SaturatedSafeIndex := {e : Coord // e ∈ saturatedSafeCoords}

theorem commonRoots_union_newHoles_card :
    (commonRoots ∪ newHoles).card = 3 * d := by
  rw [Finset.card_union_of_disjoint commonRoots_disjoint_newHoles,
    commonRoots_card, newHoles_card]
  omega

theorem hole_mem_univ_sdiff_commonRoots_union_newHoles :
    hole ∈ (Finset.univ : Finset Coord) \ (commonRoots ∪ newHoles) := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  push Not
  exact ⟨hole_not_mem_commonRoots, hole_not_mem_newHoles⟩

theorem saturatedSafeIndex_card :
    Fintype.card SaturatedSafeIndex = N - 2 * d - (d + 1) := by
  rw [Fintype.card_coe, saturatedSafeCoords,
    Finset.card_erase_of_mem (by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union]
      push Not
      exact ⟨hole_not_mem_commonRoots, hole_not_mem_newHoles⟩),
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    card_coord, commonRoots_union_newHoles_card]
  norm_num [N, d, m]

theorem saturatedSafeIndex_ne_hole (e : SaturatedSafeIndex) :
    (e : Coord) ≠ hole := by
  rcases e with ⟨e, hmem⟩
  simp only [saturatedSafeCoords, Finset.mem_erase] at hmem
  exact hmem.1

theorem saturatedSafeIndex_not_mem_commonRoots (e : SaturatedSafeIndex) :
    (e : Coord) ∉ commonRoots := by
  rcases e with ⟨e, hmem⟩
  simp only [saturatedSafeCoords, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_univ, true_and] at hmem
  have hnotUnion := hmem.2
  intro hroot
  exact hnotUnion (Finset.mem_union_left newHoles hroot)

theorem saturatedSafeIndex_not_mem_newHoles (e : SaturatedSafeIndex) :
    (e : Coord) ∉ newHoles := by
  rcases e with ⟨e, hmem⟩
  simp only [saturatedSafeCoords, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_univ, true_and] at hmem
  have hnotUnion := hmem.2
  intro hnew
  exact hnotUnion (Finset.mem_union_right commonRoots hnew)

/-! ## Exact certificate cardinality -/

theorem saturatedHoleIndex_card :
    Fintype.card SaturatedHoleIndex = d + 1 := by
  rw [Fintype.card_sum, card_selectedFibreIndex, Fintype.card_fin]

abbrev SaturatedCertificate :=
  ThreePerHoleIndex SaturatedSafeIndex SaturatedHoleIndex

theorem saturatedCertificate_card :
    Fintype.card SaturatedCertificate = N + 2 := by
  rw [card_threePerHoleIndex, saturatedSafeIndex_card,
    saturatedHoleIndex_card]
  simpa [Nat.mul_comm] using maximal_amplifier_ledger.2.1

/-! ## Safe and unsafe labels -/

noncomputable def saturatedSafeGamma (e : SaturatedSafeIndex) : F :=
  P1RateQuarterScaleBadCount.safeGamma (e : Coord)

theorem saturatedSafeGamma_injective : Function.Injective saturatedSafeGamma := by
  intro e e' heq
  apply Subtype.ext
  exact P1RateQuarterScaleBadCount.safeGamma_injective heq

theorem saturatedSafeGamma_mcaEvent
    (L : CommonLocatorData) (e : SaturatedSafeIndex) :
    mcaEvent certificateCode δsat (amplifiedU L 0) (amplifiedU L 1)
      (saturatedSafeGamma e) := by
  simpa only [saturatedSafeGamma, P1RateQuarterScaleBadCount.safeGamma] using
    saturated_safe_mcaEvent L (e : Coord)
      (saturatedSafeIndex_ne_hole e)
      (saturatedSafeIndex_not_mem_newHoles e)
      (saturatedSafeIndex_not_mem_commonRoots e)

theorem saturatedUnsafeGamma_pow_N_ne_one
    (h : SaturatedHoleIndex) (i : Fin 3) :
    saturatedUnsafeGamma h i ^ N ≠ (1 : F) := by
  rw [saturatedUnsafeGamma, mul_pow,
    P1RateQuarterScaleBadCount.domain_pow_N_eq_one, mul_one]
  exact holeConstant_pow_N_ne_one (saturatedHoleKind h) i

theorem saturatedUnsafeGamma_injective :
    Function.Injective
      (fun hi : SaturatedHoleIndex × Fin 3 => saturatedUnsafeGamma hi.1 hi.2) := by
  rintro ⟨h, i⟩ ⟨h', j⟩ heq
  have heq' :
      holeConstant (saturatedHoleKind h) i * domain (saturatedHoleCoord h) =
        holeConstant (saturatedHoleKind h') j * domain (saturatedHoleCoord h') := by
    simpa only [saturatedUnsafeGamma] using heq
  have hkindLine : (saturatedHoleKind h, i) = (saturatedHoleKind h', j) :=
    holeLabel_kind_line_eq (saturatedHole_domain_pow_m h)
      (saturatedHole_domain_pow_m h') heq'
  have hkind := congrArg Prod.fst hkindLine
  have hline := congrArg Prod.snd hkindLine
  change saturatedHoleKind h = saturatedHoleKind h' at hkind
  change i = j at hline
  have hcoordField :
      domain (saturatedHoleCoord h) = domain (saturatedHoleCoord h') := by
    apply holeLabel_coordinate_eq (saturatedHoleKind h) i
    rw [← hkind, ← hline] at heq'
    exact heq'
  apply Prod.ext
  · exact saturatedHoleCoord_injective (domain.injective hcoordField)
  · exact hline

theorem saturatedUnsafeGamma_ne_safeGamma
    (h : SaturatedHoleIndex) (i : Fin 3) (e : SaturatedSafeIndex) :
    saturatedUnsafeGamma h i ≠ saturatedSafeGamma e := by
  intro heq
  apply saturatedUnsafeGamma_pow_N_ne_one h i
  rw [heq, saturatedSafeGamma]
  exact P1RateQuarterScaleBadCount.safeGamma_pow_N_eq_one (e : Coord)

/-! ## The literal `N+2` bad-label family -/

noncomputable def saturatedScalarLabel : SaturatedCertificate → F
  | Sum.inl e => saturatedSafeGamma e
  | Sum.inr hi => saturatedUnsafeGamma hi.1 hi.2

theorem saturatedScalarLabel_injective :
    Function.Injective saturatedScalarLabel := by
  intro x y heq
  rcases x with e | hi <;> rcases y with e' | hj
  · exact congrArg Sum.inl (saturatedSafeGamma_injective heq)
  · exact (saturatedUnsafeGamma_ne_safeGamma hj.1 hj.2 e heq.symm).elim
  · exact (saturatedUnsafeGamma_ne_safeGamma hi.1 hi.2 e' heq).elim
  · exact congrArg Sum.inr (saturatedUnsafeGamma_injective heq)

theorem saturatedScalarLabel_mcaEvent
    (L : CommonLocatorData) (x : SaturatedCertificate) :
    mcaEvent certificateCode δsat (amplifiedU L 0) (amplifiedU L 1)
      (saturatedScalarLabel x) := by
  rcases x with e | ⟨h, i⟩
  · exact saturatedSafeGamma_mcaEvent L e
  · exact saturated_unsafe_mcaEvent L h i

noncomputable def saturatedBadScalars : Finset F :=
  badLabelImage saturatedScalarLabel

theorem saturatedBadScalars_card : saturatedBadScalars.card = N + 2 := by
  rw [saturatedBadScalars,
    badLabelImage_card saturatedScalarLabel saturatedScalarLabel_injective,
    saturatedCertificate_card]

theorem saturatedBadScalars_mcaEvent
    (L : CommonLocatorData) {gamma : F} (hgamma : gamma ∈ saturatedBadScalars) :
    mcaEvent certificateCode δsat (amplifiedU L 0) (amplifiedU L 1) gamma := by
  simp only [saturatedBadScalars, badLabelImage, Finset.mem_image,
    Finset.mem_univ, true_and] at hgamma
  obtain ⟨x, rfl⟩ := hgamma
  exact saturatedScalarLabel_mcaEvent L x

theorem saturated_badScalar_filter_card_ge_N_add_two (L : CommonLocatorData) :
    N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent certificateCode δsat
        (amplifiedU L 0) (amplifiedU L 1) gamma).card := by
  rw [← saturatedCertificate_card]
  exact certificate_card_le_badEvent_filter_card certificateCode δsat
    (amplifiedU L) saturatedScalarLabel saturatedScalarLabel_injective
    (saturatedScalarLabel_mcaEvent L)

/-- The operational MCA ledger for any saturated common-locator data package. -/
theorem mcaDeltaStar_le_delta (L : CommonLocatorData) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ δsat := by
  exact P1.mcaDeltaStar_le_of_N_add_two_badLabels certificateCode δsat
    (amplifiedU L) saturatedScalarLabel saturatedCertificate_card
    saturatedScalarLabel_injective (saturatedScalarLabel_mcaEvent L)

/-- Unconditional operational upper ledger for the concrete symbolic common locator. -/
theorem rateQuarter_commonFactor_mcaDeltaStar_le :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ δsat :=
  mcaDeltaStar_le_delta commonLocatorData

/-- Closed-form version of the saturated common-factor endpoint. -/
theorem rateQuarter_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      (43 / 96 : ℝ≥0) + 1 / (3 * N : ℕ) := by
  rw [← delta_eq_fortyThree_over_ninetySix_correction]
  exact rateQuarter_commonFactor_mcaDeltaStar_le

/-- The common-factor endpoint is strictly below the rate-quarter Johnson radius. -/
theorem rateQuarter_commonFactor_mcaDeltaStar_lt_half :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) certificateCode
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      (1 / 2 : ℝ≥0) :=
  rateQuarter_commonFactor_mcaDeltaStar_le.trans_lt (by
    rw [delta_eq_fortyThree_over_ninetySix_correction]
    norm_num [N])

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorBadCount

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorBadCount
#print axioms saturatedCertificate_card
#print axioms saturatedScalarLabel_injective
#print axioms saturatedScalarLabel_mcaEvent
#print axioms saturated_badScalar_filter_card_ge_N_add_two
#print axioms mcaDeltaStar_le_delta
#print axioms rateQuarter_commonFactor_mcaDeltaStar_le
#print axioms rateQuarter_commonFactor_mcaDeltaStar_le_fortyThree_over_ninetySix_correction
#print axioms rateQuarter_commonFactor_mcaDeltaStar_lt_half
