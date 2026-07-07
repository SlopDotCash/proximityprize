/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R96IterConvBudgetMonotoneAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R144TwoCharacterWeilSplitMaxBudget

/-!
# Split-cap left-budget consumers for the two-character Weil route

R96 has two equivalent public faces for the multi-step Wick budget: an endpoint-budget spelling
and a left-end monotone spelling.  R146/R147 cover the endpoint-budget spelling.  This file records
the corresponding split-cap consumers for the left-end interface, keeping downstream callers from
having to re-expand the R144 max-budget adapter.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R148TwoCharacterWeilSplitLeftBudgetConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers
open ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters
open ArkLib.ProximityGap.Frontier.R144TwoCharacterWeilSplitMaxBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Split-cap hzero-free Jacobi/Weil start at `r = 2`, followed by monotone left-budget
propagation. -/
theorem iterConvEnergyWick_from_two_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B L Ctwo C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hheadBudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtwo : Ctwo ≤ 2 * C ^ 2)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hleft₂ : (m : ℝ) ≤ C * (3 : ℝ)) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (2 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_left_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 k
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hzeroCap hoffCap hheadBudget hCtwo)
    (by simpa using hleft₂)

/-- Split-cap hzero-free Jacobi/Weil start at `r = 3`, followed by monotone left-budget
propagation. -/
theorem iterConvEnergyWick_from_three_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B L Ctriple C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hheadBudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtriple : Ctriple ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hleft₃ : (m : ℝ) ≤ C * (4 : ℝ)) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact iterConvEnergyWick_add_of_prev_of_left_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 k
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzeroCap hoffCap hheadBudget hCtriple)
    (by simpa using hleft₃)

/-- Split-cap hzero-free Jacobi/Weil start at `r = 2`, propagated and consumed by the public
pointwise pure-face bound using the monotone left-budget interface. -/
theorem sup_pureFace_from_two_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B L Ctwo C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hheadBudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtwo : Ctwo ≤ 2 * C ^ 2)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hleft₂ : (m : ℝ) ≤ C * (3 : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (2 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (2 + k) * ((2 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (2 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hzeroCap hoffCap hheadBudget hCtwo)
    (iterConvBudget_window_of_left (m := m) (r := 2) (k := k) (C := C)
      hC0 (by simpa using hleft₂))
    hs

/-- Split-cap hzero-free Jacobi/Weil start at `r = 3`, propagated and consumed by the public
pointwise pure-face bound using the monotone left-budget interface. -/
theorem sup_pureFace_from_three_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (k : ℕ) {Cweil B L Ctriple C C' : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hheadBudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hCtriple : Ctriple ≤ 6 * C ^ 3)
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hleft₃ : (m : ℝ) ≤ C * (4 : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzeroCap hoffCap hheadBudget hCtriple)
    (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
      hC0 (by simpa using hleft₃))
    hs

/-! ## Axiom audit -/
#print axioms iterConvEnergyWick_from_two_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
#print axioms iterConvEnergyWick_from_three_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
#print axioms sup_pureFace_from_two_of_twoCharacterWeilInput_splitBudget_left_budget_le_const
#print axioms sup_pureFace_from_three_of_twoCharacterWeilInput_splitBudget_left_budget_le_const

end ArkLib.ProximityGap.Frontier.R148TwoCharacterWeilSplitLeftBudgetConsumers
