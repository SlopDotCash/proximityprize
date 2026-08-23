/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R61GenericTriangleBaseline

/-!
# LANE B2 (#466 round 62): monotone adapters for the triangle sextic budget

Round 61 fully discharges the all-lag sextic interface at the elementary triangle scale
`normalizedUnitSexticBudget G q³`.  This file packages that theorem with downstream-chosen
larger budgets, matching the adapter style used for the sharper conditional lanes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R62TriangleBudgetAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
open ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The triangle-scale sextic input can be used at any larger downstream scalar budget. -/
theorem sexticCorrelationBound_triangle_of_unitCharacters_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ}
    (hB : normalizedUnitSexticBudget (F := F) G ((Fintype.card F : ℝ) ^ 3) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_mono hB
    (sexticCorrelationBound_triangle_of_unitCharacters hχ hχ1 hfam hgrp)

/-- Pointwise six-`J` triangle-scale bound at any larger downstream scalar budget. -/
theorem sextic_correlation_bound_triangle_of_unitCharacters_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ}
    (hB : normalizedUnitSexticBudget (F := F) G ((Fintype.card F : ℝ) ^ 3) ≤ B)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * B :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_triangle_of_unitCharacters_le hχ hχ1 hfam hgrp hB)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy at any larger downstream triangle-derived budget. -/
theorem sextic_correlation_energy_bound_triangle_of_unitCharacters_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ}
    (hB : normalizedUnitSexticBudget (F := F) G ((Fintype.card F : ℝ) ^ 3) ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_triangle_of_unitCharacters_le hχ hχ1 hfam hgrp hB)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62TriangleBudgetAdapters.sexticCorrelationBound_triangle_of_unitCharacters_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62TriangleBudgetAdapters.sextic_correlation_bound_triangle_of_unitCharacters_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62TriangleBudgetAdapters.sextic_correlation_energy_bound_triangle_of_unitCharacters_le

end ArkLib.ProximityGap.Frontier.R62TriangleBudgetAdapters
