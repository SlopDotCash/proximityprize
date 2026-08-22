/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R38SexticVarietyInput

/-!
# LANE B2 (#466 round 40): the extremal class of the final input EXACT — one composition of
  landed lemmas

Round 39 found the stress-extremal shapes of `SexticVarietyInput` are the degenerate cubes:
the lag correlations of `J³`.  But `J³ = c_{f₀^{⊛3}}` (round 36), so the master identity
(rounds 32–33) collapses them exactly:

  **`cube_lag_correlation_exact`** :
  `∑_j J_{j+t}³·conj(J_j³) = m·∑_{u∈G}∑_w f₀^{⊛3}(u·w)·conj(f₀^{⊛3}(w))·λ_t(w)`.

The worst case of the campaign's final named input is not an input at all — it is a theorem
of the calculus, in explicit `G`-fibered closed form.  `SexticVarietyInput` is needed only on
the generic (non-cube) shapes, where the round-39 stress margin is ample at `C = 4`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 40, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R40CubeClassExact

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation
open ArkLib.ProximityGap.Frontier.R33QuadViaWeights
open ArkLib.ProximityGap.Frontier.R35TransformRingHom
open ArkLib.ProximityGap.Frontier.R36JacobiPowers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- **THE CUBE CLASS EXACT (round-40 main theorem)** — the stress-extremal shapes of the
final named input are a theorem of the calculus. -/
theorem cube_lag_correlation_exact (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (t : ZMod m) :
    ∑ j : ZMod m, (jacobiCoeff χ lam (j + t)) ^ 3
        * (starRingEnd ℂ) ((jacobiCoeff χ lam j) ^ 3)
      = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          mulConvPow (jacobiWeight χ) 2 (u * w)
            * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w := by
  classical
  have hcube : ∀ i : ZMod m, (jacobiCoeff χ lam i) ^ 3
      = lamTransform lam (mulConvPow (jacobiWeight χ) 2) i := by
    intro i
    have := jacobiCoeff_pow (χ := χ) hfam i 2
    simpa using this
  calc ∑ j : ZMod m, (jacobiCoeff χ lam (j + t)) ^ 3
        * (starRingEnd ℂ) ((jacobiCoeff χ lam j) ^ 3)
      = ∑ j : ZMod m, lamTransform lam (mulConvPow (jacobiWeight χ) 2) (j + t)
          * (starRingEnd ℂ) (lamTransform lam (mulConvPow (jacobiWeight χ) 2) j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hcube (j + t), hcube j]
    _ = (m : ℂ) * ∑ u ∈ G, ∑ w : F,
          mulConvPow (jacobiWeight χ) 2 (u * w)
            * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w :=
        weighted_lag_correlation' hfam hgrp _ _ t

end ArkLib.ProximityGap.Frontier.R40CubeClassExact

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R40CubeClassExact.cube_lag_correlation_exact
