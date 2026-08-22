/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R144TwoCharacterWeilSplitMaxBudget

/-!
# Split-cap consequences for the R35 two-character Weil max budget

R144 turns two scalar caps into the hzero-free max-budget used by the two-character Weil bridge.
This file pushes the same split-cap certificate through the remaining R35 consequences:
the sextic moment consumer and the pointwise pure-face consumer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R145TwoCharacterWeilSplitMaxConsequences

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy
open ArkLib.ProximityGap.Frontier.R144TwoCharacterWeilSplitMaxBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Split-cap face-sextic-moment consequence of the R35 hzero-free two-character Weil bridge. -/
theorem sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B L Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    ∑ s ∈ Finset.univ.erase (0 : F),
        ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    hχ hχ1 hfam hgrp hB0 hJ hBsq hweil
    (twoCharacterWeil_maxBudget_of_split_caps
      (m := m) (G := G) (B := B) (Cweil := Cweil) (L := L)
      hzeroCap hoffCap hbudget)

/-- Split-cap pointwise pure-face consequence of the R35 hzero-free two-character Weil bridge. -/
theorem sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B L Ctriple : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (Ctriple * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  exact sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    hχ hχ1 hfam hgrp hB0 hJ hBsq hweil
    (twoCharacterWeil_maxBudget_of_split_caps
      (m := m) (G := G) (B := B) (Cweil := Cweil) (L := L)
      hzeroCap hoffCap hbudget)
    hs

/-! ## Axiom audit -/
#print axioms sextic_moment_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
#print axioms sup_pureFace_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget

end ArkLib.ProximityGap.Frontier.R145TwoCharacterWeilSplitMaxConsequences
