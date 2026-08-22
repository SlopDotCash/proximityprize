/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R32LagOffDiagEnergy

/-!
# LANE B2 (#466 round 33): normalized lag-variance budget from the Weil pair spectrum

Round 31 bounded each off-zero lag correlation.  Round 32 summed those bounds over all
nonzero lags.  This brick packages the exact downstream interface:

* `OffDiagLagVarianceBudget` names an application-level budget for the off-diagonal pair
  spectrum relative to a supplied scale `K`.
* `offDiag_lagVarianceBudget_of_weil_budget` plugs the R32 bound into any arithmetic
  budget comparison.
* `offDiag_lagVarianceBudget_normalized` records the normalized form used at prize
  scaling: once `(m-1)(m|G|C√q)^2 ≤ eps·(m q)^2`, the off-diagonal pair spectrum is
  `eps`-small relative to the lag-zero Jacobi scale `m q`.

This is not a closure of the prize wall; it is the exact bridge that lets later
structured/random decompositions consume the pair-correlation cancellation without
re-proving the R30/R31/R32 algebra.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R33LagVarianceBudget

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound
open ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- A named budget for the off-diagonal `L²` mass of the Jacobi lag correlations. -/
def OffDiagLagVarianceBudget (χ : F → ℂ) (lam : ZMod m → F → ℂ) (K : ℝ) : Prop :=
  ∑ t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
      ‖lagCorrelation χ lam t‖ ^ 2 ≤ K

/-- The R32 pointwise-Weil pair spectrum bound feeds any downstream numeric budget. -/
theorem offDiag_lagVarianceBudget_of_weil_budget
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C K : ℝ} (hC : 0 ≤ C) (hweil : TwoCharacterWeilInput χ lam G C)
    (hbudget :
      (((m : ℝ) - 1) *
        (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2)) ≤ K) :
    OffDiagLagVarianceBudget χ lam K := by
  unfold OffDiagLagVarianceBudget
  exact (offDiag_lagCorrelation_energy_bound hfam hgrp hC hweil).trans hbudget

/-- **Normalized lag-variance form.**  If the R31/R32 Weil envelope is at most
`eps·(m q)^2`, then the off-zero pair spectrum has that normalized variance budget. -/
theorem offDiag_lagVarianceBudget_normalized
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C eps : ℝ} (hC : 0 ≤ C) (hweil : TwoCharacterWeilInput χ lam G C)
    (hbudget :
      (((m : ℝ) - 1) *
        (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2))
          ≤ eps * (((m : ℝ) * (Fintype.card F : ℝ)) ^ 2)) :
    OffDiagLagVarianceBudget χ lam
      (eps * (((m : ℝ) * (Fintype.card F : ℝ)) ^ 2)) :=
  offDiag_lagVarianceBudget_of_weil_budget hfam hgrp hC hweil hbudget

end ArkLib.ProximityGap.Frontier.R33LagVarianceBudget

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R33LagVarianceBudget in
#print axioms
  offDiag_lagVarianceBudget_of_weil_budget
open ArkLib.ProximityGap.Frontier.R33LagVarianceBudget in
#print axioms
  offDiag_lagVarianceBudget_normalized
