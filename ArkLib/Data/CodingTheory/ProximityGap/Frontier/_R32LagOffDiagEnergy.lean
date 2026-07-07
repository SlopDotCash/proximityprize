/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R31LagSpectrumWeilBound

/-!
# LANE B2 (#466 round 32): off-diagonal lag energy from the Weil-small pair spectrum

Round 31 bounded each nonzero lag correlation of the Jacobi coefficient sequence.  This brick
packages the immediate `L²` consequence over all nonzero lags:

`∑_{t≠0} ‖∑_j J_{j+t}·conj(J_j)‖²
  ≤ (m - 1) · (m·|G|·C·√q)²`.

This is the pair-spectrum input in the shape consumed by structured/random or variance
decompositions.  It remains conditional on the same named two-character Weil input as R31 and
does not close the triple-and-higher correlation wall.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The lag-correlation sequence attached to the Jacobi coefficients. -/
noncomputable def lagCorrelation (χ : F → ℂ) (lam : ZMod m → F → ℂ) (t : ZMod m) : ℂ :=
  ∑ j : ZMod m, jacobiCoeff χ lam (j + t) * (starRingEnd ℂ) (jacobiCoeff χ lam j)

/-- **Off-zero pair spectrum energy.**  Under the R31 two-character Weil input, the total
energy of all nonzero lag correlations is at most `(m - 1)` times the square of the pointwise
Weil-scale bound. -/
theorem offDiag_lagCorrelation_energy_bound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hC : 0 ≤ C) (hweil : TwoCharacterWeilInput χ lam G C) :
    ∑ t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ‖lagCorrelation χ lam t‖ ^ 2
      ≤ (((m : ℝ) - 1) *
          (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2)) := by
  classical
  let B : ℝ := (m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpoint : ∀ t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
      ‖lagCorrelation χ lam t‖ ^ 2 ≤ B ^ 2 := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp ht).2
      simpa using hnot
    have hle := lag_correlation_bound hfam hgrp hweil ht0
    dsimp [lagCorrelation, B] at hle ⊢
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc ∑ t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ‖lagCorrelation χ lam t‖ ^ 2
      ≤ ∑ _t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))), B ^ 2 :=
        Finset.sum_le_sum hpoint
    _ = (((m : ℝ) - 1) * (B ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.card_sdiff]
        have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
        have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
        simp [ZMod.card, Nat.cast_sub hm1]
    _ = (((m : ℝ) - 1) *
          (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2)) := rfl

/-- **Normalized off-zero pair-spectrum RMS bound.**  Dividing the aggregate off-diagonal
energy by the number of nonzero lags recovers exactly the square of the R31 pointwise
Weil-scale budget. -/
theorem offDiag_lagCorrelation_rms_bound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hC : 0 ≤ C) (hweil : TwoCharacterWeilInput χ lam G C) (hm : 1 < m) :
    (∑ t ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ‖lagCorrelation χ lam t‖ ^ 2) / ((m : ℝ) - 1)
      ≤ (((m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F)) ^ 2) := by
  have hden : 0 < (m : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hm)
  have henergy := offDiag_lagCorrelation_energy_bound hfam hgrp hC hweil
  refine (div_le_iff₀ hden).mpr ?_
  rwa [mul_comm] at henergy

end ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy.offDiag_lagCorrelation_energy_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R32LagOffDiagEnergy.offDiag_lagCorrelation_rms_bound
