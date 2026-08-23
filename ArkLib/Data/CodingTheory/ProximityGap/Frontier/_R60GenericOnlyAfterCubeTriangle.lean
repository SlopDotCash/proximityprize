/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R58SplitCubeLagBudgetAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R59CubeLagTriangleBaseline

/-!
# LANE B2 (#466 round 60): discharge the cube side at triangle scale

Rounds 57--58 split the sextic wall into generic non-cube cancellation and cube-lag
cancellation.  Round 59 proves the cube-lag side at the elementary triangle scale `q³`.

This file composes those facts: the all-lag sextic interface now follows from only the generic
non-cube input, with downstream normalized budget evaluated at `max Cgeneric q³`.

This is still not the prize-scale theorem, since `q³` is far larger than the desired absolute
cube constant.  It does, however, make the currently discharged part of the split wall explicit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
open ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters
open ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- With the cube side discharged by triangle inequality, the all-lag R37
`SexticCorrelationBound` follows from the generic non-cube input alone, at the normalized
budget with constant `max Cgeneric q³`. -/
theorem sexticCorrelationBound_of_generic_unitCharacters_cubeTriangle
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric) :
    SexticCorrelationBound χ lam G
      (normalizedUnitSexticBudget (F := F) G
        (max Cgeneric ((Fintype.card F : ℝ) ^ 3))) :=
  sexticCorrelationBound_of_generic_cubeLag_normalizedUnitBudget_le
    hχ hχ1 hfam hgrp hgeneric
    (cubeLagInput_triangle_of_unitCharacters hχ hχ1 hfam hgrp)
    (le_max_left _ _)
    (le_max_right _ _)

/-- Pointwise six-`J` bound after discharging the cube side by triangle inequality. -/
theorem sextic_correlation_bound_of_generic_unitCharacters_cubeTriangle
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G
          (max Cgeneric ((Fintype.card F : ℝ) ^ 3)) :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_unitCharacters_cubeTriangle
      hχ hχ1 hfam hgrp hgeneric)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy after discharging the cube side by triangle inequality. -/
theorem sextic_correlation_energy_bound_of_generic_unitCharacters_cubeTriangle
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G
            (max Cgeneric ((Fintype.card F : ℝ) ^ 3))) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_unitCharacters_cubeTriangle
      hχ hχ1 hfam hgrp hgeneric)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle.sexticCorrelationBound_of_generic_unitCharacters_cubeTriangle
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle.sextic_correlation_bound_of_generic_unitCharacters_cubeTriangle
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle.sextic_correlation_energy_bound_of_generic_unitCharacters_cubeTriangle

end ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle
