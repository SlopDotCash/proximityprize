/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R35FullConvLagEnergy

/-!
# LANE B2 (#466 round 144): split caps for the R35 two-character Weil max budget

R35 exposes hzero-free Jacobi/Weil consumers for the r = 2 and r = 3 ladder, but the public
budget is written with a single `max` of the zero-lag envelope and the off-zero Weil envelope.
This adapter records the more usable certificate shape: two independent scalar caps below a
common lag budget `L` imply the existing max-budget hypotheses.

This does not close the r = 3 core; it removes one layer of arithmetic friction from the
Katz/Weil-style route into `TripleConvEnergyBound` and `IterConvEnergyWick`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R144TwoCharacterWeilSplitMaxBudget

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R35FullConvLagEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Two scalar caps imply R35's hzero-free `max` budget.  The two caps correspond to the
trivial zero-lag envelope `m B²` and the off-zero two-character Weil envelope. -/
theorem twoCharacterWeil_maxBudget_of_split_caps
    {Cweil B L Ctarget : ℝ}
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  have hmax :
      max ((m : ℝ) * B ^ 2)
          ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ≤ L :=
    max_le hzeroCap hoffCap
  have hmax0 :
      0 ≤ max ((m : ℝ) * B ^ 2)
          ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) := by
    exact le_max_of_le_left (by positivity)
  have hsq :
      (max ((m : ℝ) * B ^ 2)
          ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hmax0 hmax 2
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hmain :
      2 * ((m : ℝ)
        * (max ((m : ℝ) * B ^ 2)
            ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2))
        ≤ 2 * ((m : ℝ) * L ^ 2) := by
    gcongr
  linarith

/-- The split head-budget forces the common lag cap to fit inside the target scale.

This is the reverse arithmetic pressure behind the split-cap route: before any Weil/Katz input can
close the r = 3 face at target `Ctarget`, its common lag budget `L` must satisfy the displayed
quadratic constraint. -/
theorem split_budget_forces_lag_square_bound
    {B L Ctarget : ℝ}
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2) :
    2 * L ^ 2 ≤ Ctarget * (Fintype.card F : ℝ) ^ 2 := by
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hboundary : 0 ≤ (8 * (m : ℝ)) * B ^ 2 := by positivity
  have hmain : 2 * ((m : ℝ) * L ^ 2)
      ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
    nlinarith
  nlinarith

/-- Contrapositive form: a lag cap above the target scale cannot satisfy the split head-budget. -/
theorem not_split_budget_of_lag_square_bound_lt
    {B L Ctarget : ℝ}
    (hL : Ctarget * (Fintype.card F : ℝ) ^ 2 < 2 * L ^ 2) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  intro hbudget
  have hforced :
      2 * L ^ 2 ≤ Ctarget * (Fintype.card F : ℝ) ^ 2 :=
    split_budget_forces_lag_square_bound (m := m) (F := F)
      (B := B) (L := L) (Ctarget := Ctarget) hbudget
  nlinarith

/-- If the zero-lag scalar cap already exceeds the target scale, no common split lag budget can
both dominate it and satisfy the split head-budget. -/
theorem not_split_budget_of_zero_cap_square_bound_lt
    {B L Ctarget : ℝ}
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hzero : Ctarget * (Fintype.card F : ℝ) ^ 2 < 2 * ((m : ℝ) * B ^ 2) ^ 2) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  have hzeroNonneg : 0 ≤ (m : ℝ) * B ^ 2 := by positivity
  have hLagSq : ((m : ℝ) * B ^ 2) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hzeroNonneg hzeroCap 2
  exact not_split_budget_of_lag_square_bound_lt (m := m) (F := F)
    (B := B) (L := L) (Ctarget := Ctarget) (by nlinarith)

/-- If the off-zero Weil scalar cap already exceeds the target scale, no common split lag budget
can both dominate it and satisfy the split head-budget. -/
theorem not_split_budget_of_off_cap_square_bound_lt
    {Cweil B L Ctarget : ℝ}
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hoffNonneg : 0 ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hoff : Ctarget * (Fintype.card F : ℝ) ^ 2
      < 2 * ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  have hLagSq :
      ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hoffNonneg hoffCap 2
  exact not_split_budget_of_lag_square_bound_lt (m := m) (F := F)
    (B := B) (L := L) (Ctarget := Ctarget) (by nlinarith)

/-- Normal form for the squared off-zero two-character Weil cap. -/
theorem off_cap_square_eq
    (Cweil : ℝ) :
    ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2
      = ((m : ℝ) * (G.card : ℝ) * Cweil) ^ 2 * (Fintype.card F : ℝ) := by
  have hq0 : 0 ≤ (Fintype.card F : ℝ) := by positivity
  rw [show ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2
      = ((m : ℝ) * (G.card : ℝ) * Cweil) ^ 2
        * (Real.sqrt (Fintype.card F)) ^ 2 by ring, Real.sq_sqrt hq0]

/-- Off-zero cap no-go with the squared `sqrt q` factor normalized away. -/
theorem not_split_budget_of_off_cap_normalized_bound_lt
    {Cweil B L Ctarget : ℝ}
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hoffNonneg : 0 ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hoff : Ctarget * (Fintype.card F : ℝ) ^ 2
      < 2 * (((m : ℝ) * (G.card : ℝ) * Cweil) ^ 2 * (Fintype.card F : ℝ))) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctarget * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  refine not_split_budget_of_off_cap_square_bound_lt (m := m) (F := F) (G := G)
    (Cweil := Cweil) (B := B) (L := L) (Ctarget := Ctarget)
    hoffCap hoffNonneg ?_
  simpa [off_cap_square_eq (m := m) (F := F) (G := G) Cweil] using hoff

/-- Public r = 3 form of `split_budget_forces_lag_square_bound`: if the split budget is to be
published at Wick constant `C`, the common lag cap must satisfy `L² ≤ 3*C³*q²`. -/
theorem split_budget_forces_lag_square_bound_of_triple_const
    {B L Ctriple C : ℝ}
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    L ^ 2 ≤ 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2 := by
  have hlag :
      2 * L ^ 2 ≤ Ctriple * (Fintype.card F : ℝ) ^ 2 :=
    split_budget_forces_lag_square_bound (m := m) (F := F)
      (B := B) (L := L) (Ctarget := Ctriple) hbudget
  have htarget :
      Ctriple * (Fintype.card F : ℝ) ^ 2
        ≤ (6 * C ^ 3) * (Fintype.card F : ℝ) ^ 2 := by
    gcongr
  nlinarith

/-- Public r = 3 no-go form: if the lag cap exceeds `3*C³*q²`, no split head-budget whose
target publishes at Wick constant `C` can hold. -/
theorem not_split_budget_of_lag_square_bound_lt_triple_const
    {B L Ctriple C : ℝ}
    (hL : 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2 < L ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  intro hbudget
  have hforced :
      L ^ 2 ≤ 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2 :=
    split_budget_forces_lag_square_bound_of_triple_const (m := m) (F := F)
      (B := B) (L := L) (Ctriple := Ctriple) (C := C) hbudget hC
  nlinarith

/-- Public r = 3 zero-cap no-go form. -/
theorem not_split_budget_of_zero_cap_square_bound_lt_triple_const
    {B L Ctriple C : ℝ}
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hzero : 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2 < ((m : ℝ) * B ^ 2) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  have hzeroNonneg : 0 ≤ (m : ℝ) * B ^ 2 := by positivity
  have hLagSq : ((m : ℝ) * B ^ 2) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hzeroNonneg hzeroCap 2
  exact not_split_budget_of_lag_square_bound_lt_triple_const (m := m) (F := F)
    (B := B) (L := L) (Ctriple := Ctriple) (C := C) (by nlinarith) hC

/-- Public r = 3 off-zero Weil cap no-go form. -/
theorem not_split_budget_of_off_cap_square_bound_lt_triple_const
    {Cweil B L Ctriple C : ℝ}
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hoffNonneg : 0 ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hoff : 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2
      < ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  have hLagSq :
      ((m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F)) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hoffNonneg hoffCap 2
  exact not_split_budget_of_lag_square_bound_lt_triple_const (m := m) (F := F)
    (B := B) (L := L) (Ctriple := Ctriple) (C := C) (by nlinarith) hC

/-- Public r = 3 off-zero Weil cap no-go with the squared `sqrt q` factor normalized away. -/
theorem not_split_budget_of_off_cap_normalized_bound_lt_triple_const
    {Cweil B L Ctriple C : ℝ}
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hoffNonneg : 0 ≤ (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F))
    (hoff : 3 * C ^ 3 * (Fintype.card F : ℝ) ^ 2
      < ((m : ℝ) * (G.card : ℝ) * Cweil) ^ 2 * (Fintype.card F : ℝ))
    (hC : Ctriple ≤ 6 * C ^ 3) :
    ¬ 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
        ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
  refine not_split_budget_of_off_cap_square_bound_lt_triple_const
    (m := m) (F := F) (G := G) (Cweil := Cweil) (B := B) (L := L)
    (Ctriple := Ctriple) (C := C) hoffCap hoffNonneg ?_ hC
  simpa [off_cap_square_eq (m := m) (F := F) (G := G) Cweil] using hoff

/-- Split-cap form of the R35 hzero-free Jacobi/Weil bridge into `TripleConvEnergyBound`. -/
theorem tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
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
    TripleConvEnergyBound (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) Ctriple :=
  tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    hχ hχ1 hfam hgrp hB0 hJ hBsq hweil
    (twoCharacterWeil_maxBudget_of_split_caps
      (m := m) (G := G) (B := B) (Cweil := Cweil) (L := L)
      hzeroCap hoffCap hbudget)

/-- Split-cap direct consumer for the second rung of the final convolution ladder. -/
theorem iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B L Ctwo C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctwo * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctwo ≤ 2 * C ^ 2) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 2 C :=
  iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    hχ hχ1 hfam hgrp hB0 hJ hweil
    (twoCharacterWeil_maxBudget_of_split_caps
      (m := m) (G := G) (B := B) (Cweil := Cweil) (L := L)
      hzeroCap hoffCap hbudget)
    hC

/-- Split-cap direct consumer for the calibrated third rung of the final convolution ladder. -/
theorem iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cweil B L Ctriple C : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ c : ZMod m, ‖jacobiCoeff χ lam c‖ ≤ B)
    (hBsq : B ^ 2 ≤ (Fintype.card F : ℝ))
    (hweil : TwoCharacterWeilInput χ lam G Cweil)
    (hzeroCap : (m : ℝ) * B ^ 2 ≤ L)
    (hoffCap :
      (m : ℝ) * (G.card : ℝ) * Cweil * Real.sqrt (Fintype.card F) ≤ L)
    (hbudget : 2 * ((m : ℝ) * L ^ 2) + (8 * (m : ℝ)) * B ^ 2
      ≤ Ctriple * (m : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (hC : Ctriple ≤ 6 * C ^ 3) :
    IterConvEnergyWick (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_maxBudget
    hχ hχ1 hfam hgrp hB0 hJ hBsq hweil
    (twoCharacterWeil_maxBudget_of_split_caps
      (m := m) (G := G) (B := B) (Cweil := Cweil) (L := L)
      hzeroCap hoffCap hbudget)
    hC

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms twoCharacterWeil_maxBudget_of_split_caps
#print axioms split_budget_forces_lag_square_bound
#print axioms not_split_budget_of_lag_square_bound_lt
#print axioms not_split_budget_of_zero_cap_square_bound_lt
#print axioms not_split_budget_of_off_cap_square_bound_lt
#print axioms off_cap_square_eq
#print axioms not_split_budget_of_off_cap_normalized_bound_lt
#print axioms split_budget_forces_lag_square_bound_of_triple_const
#print axioms not_split_budget_of_lag_square_bound_lt_triple_const
#print axioms not_split_budget_of_zero_cap_square_bound_lt_triple_const
#print axioms not_split_budget_of_off_cap_square_bound_lt_triple_const
#print axioms not_split_budget_of_off_cap_normalized_bound_lt_triple_const
#print axioms tripleConvEnergyBound_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
#print axioms iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget
#print axioms iterConvEnergyWick_three_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget

end ArkLib.ProximityGap.Frontier.R144TwoCharacterWeilSplitMaxBudget
