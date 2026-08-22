/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30LagCorrelationIdentity

/-!
# LANE B2 (#466 round 31): the pair spectrum is Weil-small — the machine-checked bound the
  structured+random decomposition consumes

Round 30 evaluated every lag correlation exactly.  This brick lands the conditional bound:

  **`lag_correlation_bound`** :  under the named two-character Weil input (the round-17
  class), for every lag `t ≠ 0`:  `‖∑_j J_{j+t}·conj(J_j)‖ ≤ m·|G|·C·√q`.

Normalized against `∑_j‖J_j‖² ≈ m·q` (Jacobi–Parseval, r20), the pair spectrum off lag 0 is
`≤ n·C/√q` — vanishing at prize scaling.  This is the exact, citable form of the round-30
verdict: the structured (pair) part of the Jacobi sequence is Weil-controlled; all remaining
openness in `TripleConvEnergyBound` lives in triple-and-higher correlations.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 31, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- **Named input (two-character Weil, round-17 class)**: each inner sum of the round-30
identity has square-root cancellation, uniformly over `u ∈ G` and lags `t ≠ 0`.
(For `u = 1` the sum is elementary — `≤ 2` — so the input is classical throughout.) -/
def TwoCharacterWeilInput (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ t : ZMod m, t ≠ 0 →
    ‖∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y‖
      ≤ C * Real.sqrt (Fintype.card F)

/-- **THE PAIR-SPECTRUM BOUND (round-31 main theorem).**  Under the named input, every
off-zero lag correlation of the ladder's coefficient sequence satisfies
`‖∑_j J_{j+t}·conj(J_j)‖ ≤ m·|G|·C·√q` — Weil-scale, vanishing at prize scaling relative to
the lag-0 value `∑‖J‖² ≈ m·q`.  The structured part of the sequence is controlled;
the open core is triple-and-higher correlations only. -/
theorem lag_correlation_bound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hweil : TwoCharacterWeilInput χ lam G C)
    {t : ZMod m} (ht : t ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t) * (starRingEnd ℂ) (jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F) := by
  rw [lag_correlation_identity hfam hgrp t]
  rw [norm_mul, Complex.norm_natCast]
  have hsum : ‖∑ u ∈ G, ∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y‖
      ≤ (G.card : ℝ) * (C * Real.sqrt (Fintype.card F)) := by
    calc ‖∑ u ∈ G, ∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y‖
        ≤ ∑ u ∈ G, ‖∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _u ∈ G, C * Real.sqrt (Fintype.card F) :=
          Finset.sum_le_sum (fun u hu => hweil u hu t ht)
      _ = (G.card : ℝ) * (C * Real.sqrt (Fintype.card F)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (m : ℝ) * ‖∑ u ∈ G, ∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y‖
      ≤ (m : ℝ) * ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F))) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ) * (G.card : ℝ) * C * Real.sqrt (Fintype.card F) := by ring

end ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R31LagSpectrumWeilBound.lag_correlation_bound
