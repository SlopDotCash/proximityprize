/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R52CharacterSexticEnvelope

/-!
# LANE B2 (#466 round 53): discharge the λ-envelope from the dual-family API

Round 52 reduced the sextic zero-lag adapter to a character envelope and an abstract λ-family
envelope.  The λ envelope is already present in the substrate: `SubgroupDualFamily.map_zero`
handles the origin and `DualFamilyGroupLaw.norm_one` gives unit modulus away from the origin.

This leaves the R37 all-lag sextic correlation consumer depending only on:

* the nonzero-lag `SexticVarietyInput`,
* a pointwise envelope for `χ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The bundled dual-family hypotheses give the uniform λ-envelope `‖λ_t z‖ ≤ 1`. -/
theorem norm_lam_le_one_of_dualFamily
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (t : ZMod m) (z : F) :
    ‖lam t z‖ ≤ 1 := by
  by_cases hz : z = 0
  · rw [hz, hfam.map_zero t]
    norm_num
  · rw [hgrp.norm_one t z hz]

/-- R52 with the λ-envelope supplied by the dual-family API. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C A B : ℝ} (hA0 : 0 ≤ A)
    (hweil : SexticVarietyInput χ lam G C)
    (hχ : ∀ x : F, ‖χ x‖ ≤ A)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * (A * 1) ^ 3) ^ 2 * 1))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelopes
    hA0
    (by norm_num)
    hweil
    hχ
    (norm_lam_le_one_of_dualFamily hfam hgrp)
    hbudget

/-- Same consumer as
`sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope`, with the λ-envelope
budget simplified using `L = 1`. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope'
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C A B : ℝ} (hA0 : 0 ≤ A)
    (hweil : SexticVarietyInput χ lam G C)
    (hχ : ∀ x : F, ‖χ x‖ ≤ A)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * A ^ 3) ^ 2))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope
    hfam hgrp hA0 hweil hχ (by
      simpa using hbudget)

/-- Aggregate all-lag six-J energy from the nonzero-lag sextic variety input and an arbitrary
pointwise character envelope.  This is the R53 analogue of the unit-character R55 consumer. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_and_characterEnvelope
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C A B : ℝ} (hA0 : 0 ≤ A)
    (hweil : SexticVarietyInput χ lam G C)
    (hχ : ∀ x : F, ‖χ x‖ ≤ A)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * A ^ 3) ^ 2))) ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope'
      hfam hgrp hA0 hweil hχ hbudget)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope.norm_lam_le_one_of_dualFamily
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelope'
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope.sextic_correlation_energy_bound_of_sexticVarietyInput_and_characterEnvelope

end ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope
