/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R53DualFamilySexticEnvelope

/-!
# LANE B2 (#466 round 54): normalized character envelopes for the sextic adapter

Round 53 leaves the zero-lag sextic adapter depending on a pointwise envelope for the
multiplicative character `χ`.  For the normalized character package used throughout the ladder,
that envelope is the unit bound: zero at the origin and unit modulus away from it.

The resulting consumer reduces the all-lag R37 `SexticCorrelationBound` to the nonzero-lag
`SexticVarietyInput` plus the existing dual-family and normalized-character hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- A normalized multiplicative character is pointwise bounded by one. -/
theorem norm_character_le_one (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1) (x : F) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, hχ.map_zero]
  · exact le_of_eq (norm_chi_eq_one hχ hχ1 hx)

/-- The R37 all-lag sextic input follows from the nonzero-lag sextic variety input with only
the standard unit character/dual-family hypotheses. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C B : ℝ}
    (hweil : SexticVarietyInput χ lam G C)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * (1 : ℝ) ^ 3) ^ 2))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope'
    hfam hgrp (by norm_num) hweil
    (norm_character_le_one hχ hχ1)
    hbudget

set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope.norm_character_le_one
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_unitCharacters

end ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope
