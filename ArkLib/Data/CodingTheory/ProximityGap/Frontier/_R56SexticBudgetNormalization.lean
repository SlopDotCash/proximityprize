/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R55SexticExplicitBudget

/-!
# LANE B2 (#466 round 56): normalized explicit sextic budget

Round 55 chooses the exact unit-character budget delivered by the sextic chain.  This file
records the same budget without the formal `(1 : ℝ)^3` envelope artifact, so downstream
statements can cite the compact scalar expression directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R55SexticExplicitBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The R55 unit sextic budget with the formal unit envelope simplified away. -/
noncomputable def normalizedUnitSexticBudget (G : Finset F) (C : ℝ) : ℝ :=
  max
    ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
      * (Fintype.card F : ℝ) ^ 2))
    ((G.card : ℝ) * ((Fintype.card F : ℝ)
      * ((Fintype.card F : ℝ) ^ 2) ^ 2))

/-- The normalized and R55 explicit unit budgets are definitionally the same after arithmetic
simplification. -/
theorem normalizedUnitSexticBudget_eq_unitSexticBudget (G : Finset F) (C : ℝ) :
    normalizedUnitSexticBudget (F := F) G C = unitSexticBudget (F := F) G C := by
  unfold normalizedUnitSexticBudget unitSexticBudget
  ring_nf

/-- The normalized unit sextic budget is monotone in the nonzero-lag cancellation constant. -/
theorem normalizedUnitSexticBudget_mono (G : Finset F) {C C' : ℝ} (hC : C ≤ C') :
    normalizedUnitSexticBudget (F := F) G C
      ≤ normalizedUnitSexticBudget (F := F) G C' := by
  unfold normalizedUnitSexticBudget
  refine max_le ?_ (le_max_right _ _)
  have hscale_nonneg :
      0 ≤ Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by positivity
  have hinner :
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
        ≤ C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    calc
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
          = C * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring
      _ ≤ C' * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hC hscale_nonneg
      _ = C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring
  exact le_trans (mul_le_mul_of_nonneg_left hinner (by positivity)) (le_max_left _ _)

/-- R55's explicit all-lag `SexticCorrelationBound`, stated at the normalized budget. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ}
    (hweil : SexticVarietyInput χ lam G C) :
    SexticCorrelationBound χ lam G (normalizedUnitSexticBudget (F := F) G C) := by
  rw [normalizedUnitSexticBudget_eq_unitSexticBudget]
  exact sexticCorrelationBound_of_sexticVarietyInput_unitBudget hχ hχ1 hfam hgrp hweil

/-- R55's explicit all-lag `SexticCorrelationBound`, transported to a larger normalized
nonzero-lag cancellation constant. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC : C ≤ C')
    (hweil : SexticVarietyInput χ lam G C) :
    SexticCorrelationBound χ lam G (normalizedUnitSexticBudget (F := F) G C') :=
  sexticCorrelationBound_mono
    (normalizedUnitSexticBudget_mono (F := F) G hCC)
    (sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget
      hχ hχ1 hfam hgrp hweil)

/-- Pointwise six-`J` bound at the normalized unit budget. -/
theorem sextic_correlation_bound_of_sexticVarietyInput_normalizedUnitBudget
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
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G C := by
  rw [normalizedUnitSexticBudget_eq_unitSexticBudget]
  exact sextic_correlation_bound_of_sexticVarietyInput_unitBudget
    hχ hχ1 hfam hgrp hweil a b a' b' t

/-- Pointwise six-`J` bound after enlarging the normalized nonzero-lag cancellation constant. -/
theorem sextic_correlation_bound_of_sexticVarietyInput_normalizedUnitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC : C ≤ C')
    (hweil : SexticVarietyInput χ lam G C)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G C' :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget_le
      hχ hχ1 hfam hgrp hCC hweil)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy bound at the normalized unit budget. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_normalizedUnitBudget
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
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G C) ^ 2) := by
  rw [normalizedUnitSexticBudget_eq_unitSexticBudget]
  exact sextic_correlation_energy_bound_of_sexticVarietyInput_unitBudget
    hχ hχ1 hfam hgrp hweil

/-- Aggregate all-lag six-`J` energy bound after enlarging the normalized nonzero-lag
cancellation constant. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_normalizedUnitBudget_le
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C C' : ℝ} (hCC : C ≤ C')
    (hweil : SexticVarietyInput χ lam G C) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G C') ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget_le
      hχ hχ1 hfam hgrp hCC hweil)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.normalizedUnitSexticBudget_eq_unitSexticBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.normalizedUnitSexticBudget_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sexticCorrelationBound_of_sexticVarietyInput_normalizedUnitBudget_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sextic_correlation_bound_of_sexticVarietyInput_normalizedUnitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sextic_correlation_bound_of_sexticVarietyInput_normalizedUnitBudget_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sextic_correlation_energy_bound_of_sexticVarietyInput_normalizedUnitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization.sextic_correlation_energy_bound_of_sexticVarietyInput_normalizedUnitBudget_le

end ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
