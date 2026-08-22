/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R54CharacterUnitSexticEnvelope

/-!
# LANE B2 (#466 round 55): explicit all-lag sextic budget

Rounds 49--54 reduced the zero-lag bookkeeping to unit character envelopes.  This file removes
the final scalar bookkeeping hypothesis by choosing the exact `max` budget delivered by the
chain.  The only mathematical input left is the nonzero-lag `SexticVarietyInput`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The explicit all-lag sextic budget delivered by the unit-envelope chain. -/
noncomputable def unitSexticBudget (G : Finset F) (C : ℝ) : ℝ :=
  max
    ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
      * (Fintype.card F : ℝ) ^ 2))
    ((G.card : ℝ) * ((Fintype.card F : ℝ)
      * (((Fintype.card F : ℝ) ^ 2 * (1 : ℝ) ^ 3) ^ 2)))

/-- The explicit unit-envelope budget is monotone in the nonzero-lag variety constant. -/
theorem unitSexticBudget_mono {C C' : ℝ} (hCC' : C ≤ C') :
    unitSexticBudget (F := F) G C ≤ unitSexticBudget (F := F) G C' := by
  unfold unitSexticBudget
  refine max_le_max ?_ le_rfl
  have hscale : 0 ≤ Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    positivity
  have hinner :
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
        ≤ C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    calc
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
          = C * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring
      _ ≤ C' * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hCC' hscale
      _ = C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring
  exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-- Under the standard unit character/dual-family hypotheses, the named nonzero-lag
`SexticVarietyInput` supplies the R37 all-lag `SexticCorrelationBound` at the explicit budget
`unitSexticBudget`. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_unitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hweil : SexticVarietyInput χ lam G C) :
    SexticCorrelationBound χ lam G (unitSexticBudget (F := F) G C) :=
  sexticCorrelationBound_of_sexticVarietyInput_and_unitCharacters
    hχ hχ1 hfam hgrp hweil (le_rfl)

/-- A version with a larger downstream budget. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_unitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C B : ℝ}
    (hweil : SexticVarietyInput χ lam G C)
    (hB : unitSexticBudget (F := F) G C ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_mono hB
    (sexticCorrelationBound_of_sexticVarietyInput_unitBudget hχ hχ1 hfam hgrp hweil)

/-- A variety input at a sharper constant can be published at any larger explicit unit budget. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_unitBudget_mono
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C C' : ℝ}
    (hCC' : C ≤ C')
    (hweil : SexticVarietyInput χ lam G C) :
    SexticCorrelationBound χ lam G (unitSexticBudget (F := F) G C') :=
  sexticCorrelationBound_of_sexticVarietyInput_unitBudget_le hχ hχ1 hfam hgrp hweil
    (unitSexticBudget_mono (F := F) (G := G) hCC')

/-- Pointwise six-`J` bound at the explicit unit-envelope budget. -/
theorem sextic_correlation_bound_of_sexticVarietyInput_unitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hweil : SexticVarietyInput χ lam G C)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * unitSexticBudget (F := F) G C :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_unitBudget hχ hχ1 hfam hgrp hweil)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy bound at the explicit unit-envelope budget. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget
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
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_unitBudget hχ hχ1 hfam hgrp hweil)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.unitSexticBudget_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.sexticCorrelationBound_of_sexticVarietyInput_unitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.sexticCorrelationBound_of_sexticVarietyInput_unitBudget_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.sexticCorrelationBound_of_sexticVarietyInput_unitBudget_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.sextic_correlation_bound_of_sexticVarietyInput_unitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget.sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget

end ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget
