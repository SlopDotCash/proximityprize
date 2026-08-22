/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55SexticExplicitBudget

/-!
# LANE B2 (#466 round 55): unit-character sextic variety input gives sextic energy

Round 54 reduced the all-lag `SexticCorrelationBound` to the nonzero-lag
`SexticVarietyInput` plus the standard normalized-character and dual-family hypotheses.  This
file immediately feeds that into the R37 aggregate energy consumer, giving the all-lag six-J
energy estimate in the same normalized-character setting.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R55UnitSexticEnergy

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope
open ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Aggregate all-lag six-J energy from the nonzero-lag sextic variety input, with the
zero-lag and unit-envelope bookkeeping discharged by rounds 49-54. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters
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
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_and_unitCharacters
      hχ hχ1 hfam hgrp hweil hbudget)

/-- Same aggregate sextic-energy consumer as
`sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters`, with the unit
envelope budget simplified. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C B : ℝ}
    (hweil : SexticVarietyInput χ lam G C)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * ((Fintype.card F : ℝ) ^ 2) ^ 2)) ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters
    hχ hχ1 hfam hgrp hweil (by
      simpa using hbudget)

/-- Aggregate sextic-energy consumer at the canonical explicit unit-envelope budget. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget'
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hweil : SexticVarietyInput χ lam G C) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * unitSexticBudget (F := F) G C) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget
    hχ hχ1 hfam hgrp hweil

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55UnitSexticEnergy.sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55UnitSexticEnergy.sextic_correlation_energy_bound_of_sexticVarietyInput_and_unitCharacters'
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55UnitSexticEnergy.sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget'

end ArkLib.ProximityGap.Frontier.R55UnitSexticEnergy
