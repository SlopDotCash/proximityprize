/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R63SplitInputMonotonicity

/-!
# LANE B2 (#466 round 64): consumers for separately landed split constants

Rounds 62--63 isolate the prize-facing cancellation lever and prove monotonicity for each split
input.  This file packages the form most useful for future analytic work: a generic estimate
with constant `Cgeneric` and a cube-lag estimate with constant `Ccube` immediately imply the
normalized all-lag sextic bounds at `max Cgeneric Ccube`, or at any larger common constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
open ArkLib.ProximityGap.Frontier.R62SplitSavingLever
open ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Separately proved generic and cube-lag cancellation estimates imply the normalized all-lag
`SexticCorrelationBound` at the maximum of their constants. -/
theorem sexticCorrelationBound_of_generic_cubeLag_max
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube) :
    SexticCorrelationBound χ lam G
      (normalizedUnitSexticBudget (F := F) G (max Cgeneric Ccube)) :=
  sexticCorrelationBound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_max hgeneric hcube)

/-- Pointwise six-`J` bound from separate generic/cube-lag constants, normalized at their max. -/
theorem sextic_correlation_bound_of_generic_cubeLag_max
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G (max Cgeneric Ccube) :=
  sextic_correlation_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_max hgeneric hcube)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy from separate generic/cube-lag constants, normalized at
their max. -/
theorem sextic_correlation_energy_bound_of_generic_cubeLag_max
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G
            (max Cgeneric Ccube)) ^ 2) :=
  sextic_correlation_energy_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_max hgeneric hcube)

/-- Separately proved generic and cube-lag estimates bounded by a chosen common `C` imply the
normalized all-lag interface at `C`. -/
theorem sexticCorrelationBound_of_generic_cubeLag_common_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube C : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hCg : Cgeneric ≤ C) (hCc : Ccube ≤ C) :
    SexticCorrelationBound χ lam G (normalizedUnitSexticBudget (F := F) G C) :=
  sexticCorrelationBound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_le hgeneric hcube hCg hCc)

/-- Pointwise six-`J` bound from separate split estimates bounded by a chosen common `C`. -/
theorem sextic_correlation_bound_of_generic_cubeLag_common_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube C : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hCg : Cgeneric ≤ C) (hCc : Ccube ≤ C)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G C :=
  sextic_correlation_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_le hgeneric hcube hCg hCc)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy from separate split estimates bounded by a chosen
common `C`. -/
theorem sextic_correlation_energy_bound_of_generic_cubeLag_common_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube C : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hCg : Cgeneric ≤ C) (hCc : Ccube ≤ C) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G C) ^ 2) :=
  sextic_correlation_energy_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_of_generic_cubeLag_le hgeneric hcube hCg hCc)

/-- A split cancellation input at `C₀` supplies the normalized all-lag interface at any larger
constant `C`. -/
theorem sexticCorrelationBound_of_splitSexticCancellationInput_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C₀ C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C₀) (hC : C₀ ≤ C) :
    SexticCorrelationBound χ lam G (normalizedUnitSexticBudget (F := F) G C) :=
  sexticCorrelationBound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_mono hC hsplit)

/-- Pointwise six-`J` bound from a split cancellation input lifted to any larger normalized
constant. -/
theorem sextic_correlation_bound_of_splitSexticCancellationInput_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C₀ C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C₀) (hC : C₀ ≤ C)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G C :=
  sextic_correlation_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_mono hC hsplit) a b a' b' t

/-- Aggregate all-lag six-`J` energy from a split cancellation input lifted to any larger
normalized constant. -/
theorem sextic_correlation_energy_bound_of_splitSexticCancellationInput_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C₀ C : ℝ}
    (hsplit : SplitSexticCancellationInput χ lam G C₀) (hC : C₀ ≤ C) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G C) ^ 2) :=
  sextic_correlation_energy_bound_of_splitSexticCancellationInput hχ hχ1 hfam hgrp
    (splitSexticCancellationInput_mono hC hsplit)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sexticCorrelationBound_of_generic_cubeLag_max
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_bound_of_generic_cubeLag_max
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_energy_bound_of_generic_cubeLag_max
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sexticCorrelationBound_of_generic_cubeLag_common_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_bound_of_generic_cubeLag_common_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_energy_bound_of_generic_cubeLag_common_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sexticCorrelationBound_of_splitSexticCancellationInput_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_bound_of_splitSexticCancellationInput_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers.sextic_correlation_energy_bound_of_splitSexticCancellationInput_le

end ArkLib.ProximityGap.Frontier.R64SeparateConstantSplitConsumers
