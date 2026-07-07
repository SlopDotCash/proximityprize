/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R57SplitCubeLagUnitBudget

/-!
# LANE B2 (#466 round 58): monotone adapters for the split cube-lag budget

Round 57 exposes an explicit all-lag sextic budget from the split generic/cube-lag
nonzero-lag inputs plus unit-character zero-lag bookkeeping.  This file packages the same
result with downstream-chosen larger budgets, mirroring the R55 explicit-budget adapters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The split generic/cube-lag input supplies `SexticCorrelationBound` at any larger
downstream budget. -/
theorem sexticCorrelationBound_of_generic_cubeLag_unitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube B : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hB : splitCubeLagUnitBudget (F := F) G Cgeneric Ccube ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_mono hB
    (sexticCorrelationBound_of_generic_cubeLag_unitBudget
      hχ hχ1 hfam hgrp hgeneric hcube)

/-- Pointwise six-`J` bound from the split generic/cube-lag input at any larger downstream
budget. -/
theorem sextic_correlation_bound_of_generic_cubeLag_unitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube B : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hB : splitCubeLagUnitBudget (F := F) G Cgeneric Ccube ≤ B)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * B :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_cubeLag_unitBudget_le
      hχ hχ1 hfam hgrp hgeneric hcube hB)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy from the split generic/cube-lag input at any larger
downstream budget. -/
theorem sextic_correlation_energy_bound_of_generic_cubeLag_unitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube B : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hB : splitCubeLagUnitBudget (F := F) G Cgeneric Ccube ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_cubeLag_unitBudget_le
      hχ hχ1 hfam hgrp hgeneric hcube hB)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters.sexticCorrelationBound_of_generic_cubeLag_unitBudget_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters.sextic_correlation_bound_of_generic_cubeLag_unitBudget_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters.sextic_correlation_energy_bound_of_generic_cubeLag_unitBudget_le

end ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters
