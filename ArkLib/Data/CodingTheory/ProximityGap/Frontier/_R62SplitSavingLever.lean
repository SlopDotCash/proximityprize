/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R58SplitCubeLagBudgetAdapters

/-!
# LANE B2 (#466 round 62): the split sextic saving lever

Round 61 discharges the split sextic route at the triangle-inequality scale `q³`.  This file
records the exact remaining cancellation lever: a common constant for the generic non-cube
sextic variety input and the cube-lag input.  Once those two split estimates are supplied with
an absolute constant `C`, the normalized all-lag sextic bound follows immediately.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R62SplitSavingLever

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
open ArkLib.ProximityGap.Frontier.R58SplitCubeLagBudgetAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The common-constant cancellation input left by the split sextic route: the generic
non-cube fibers and the cube-lag fibers both satisfy square-root cancellation with constant
`C`.  The proximity-prize content is to provide this with `C` independent of `F`, `G`, and
the lag parameters. -/
def SplitSexticCancellationInput
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (C : ℝ) : Prop :=
  GenericSexticVarietyInput χ lam G C ∧ CubeLagInput χ lam G C

/-- A split sextic cancellation input at constant `C` implies the normalized all-lag
`SexticCorrelationBound` at the same constant. -/
theorem sexticCorrelationBound_of_splitSexticCancellationInput
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C) :
    SexticCorrelationBound χ lam G (normalizedUnitSexticBudget (F := F) G C) :=
  sexticCorrelationBound_of_generic_cubeLag_normalizedUnitBudget_le
    hχ hχ1 hfam hgrp hsplit.1 hsplit.2 le_rfl le_rfl

/-- Pointwise six-`J` consequence of a common-constant split sextic cancellation input. -/
theorem sextic_correlation_bound_of_splitSexticCancellationInput
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G C :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp hsplit)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy consequence of a common-constant split sextic
cancellation input. -/
theorem sextic_correlation_energy_bound_of_splitSexticCancellationInput
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G C) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp hsplit)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62SplitSavingLever.SplitSexticCancellationInput
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62SplitSavingLever.sexticCorrelationBound_of_splitSexticCancellationInput
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62SplitSavingLever.sextic_correlation_bound_of_splitSexticCancellationInput
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R62SplitSavingLever.sextic_correlation_energy_bound_of_splitSexticCancellationInput

end ArkLib.ProximityGap.Frontier.R62SplitSavingLever
