/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R96IterConvEndpointBudgetConsumers
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R144TwoCharacterWeilSplitMaxBudget

/-!
# Split-cap endpoint consumers for the R35 two-character Weil route

R96 propagates an R35 max-budget head certificate to deeper convolution rungs using a single
endpoint budget.  R144 replaces the R35 max-budget premise by two independent scalar caps.
This file composes the two interfaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R146TwoCharacterWeilSplitEndpointConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R96IterConvEndpointBudgetConsumers
open ArkLib.ProximityGap.Frontier.R144TwoCharacterWeilSplitMaxBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Split-cap hzero-free Jacobi/Weil start at `r = 2`, followed by R96 endpoint propagation. -/
theorem iterConvEnergyWick_from_two_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
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
    (hbudget₂ : (m : ℝ) ≤ C * 3) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (2 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 k
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hzeroCap hoffCap hheadBudget hCtwo)
    (by simpa using hbudget₂)

/-- Split-cap hzero-free Jacobi/Weil start at `r = 3`, followed by R96 endpoint propagation. -/
theorem iterConvEnergyWick_from_three_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
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
    (hbudget₃ : (m : ℝ) ≤ C * 4) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact iterConvEnergyWick_add_of_prev_of_endpoint_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 k
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzeroCap hoffCap hheadBudget hCtriple)
    (by simpa using hbudget₃)

/-- Split-cap hzero-free Jacobi/Weil start at `r = 2`, propagated and consumed by the public
pointwise pure-face endpoint bound. -/
theorem sup_pureFace_from_two_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
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
    (hbudget₂ : (m : ℝ) ≤ C * 3)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (2 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (2 + k) * ((2 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (2 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hweil hzeroCap hoffCap hheadBudget hCtwo)
    (by simpa using hbudget₂) hs

/-- Split-cap hzero-free Jacobi/Weil start at `r = 3`, propagated and consumed by the public
pointwise pure-face endpoint bound. -/
theorem sup_pureFace_from_three_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
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
    (hbudget₃ : (m : ℝ) ≤ C * 4)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) := by
  have hJsq : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro c
    exact (pow_le_pow_left₀ (norm_nonneg _) (hJ c) 2).trans hBsq
  exact sup_pureFace_add_of_iterConvEnergyWick_prev_of_endpoint_budget_le_const
    hfam hgrp (fun i : ZMod m => jacobiCoeff χ lam i)
    hJsq hC0 hCC
    (iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
      hχ hχ1 hfam hgrp hB0 hJ hBsq hweil hzeroCap hoffCap hheadBudget hCtriple)
    (by simpa using hbudget₃) hs

/-! ## Axiom audit -/
#print axioms iterConvEnergyWick_from_two_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
#print axioms iterConvEnergyWick_from_three_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
#print axioms sup_pureFace_from_two_of_twoCharacterWeilInput_splitBudget_endpoint_le_const
#print axioms sup_pureFace_from_three_of_twoCharacterWeilInput_splitBudget_endpoint_le_const

end ArkLib.ProximityGap.Frontier.R146TwoCharacterWeilSplitEndpointConsumers
