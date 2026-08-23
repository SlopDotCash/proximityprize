/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R41SexticInputSplit

/-!
# LANE B2 (#466 round 42): cube input as the concrete `J³` lag input

Round 41 split the final sextic input into generic shapes and the degenerate cube shape.
This file identifies the cube shape in the R38/R41 input with the concrete multiplicative
convolution weight `f₀^{⊛3}` already used by the round-40 exact `J³` lag identity.

The payoff is proof plumbing: the final cube-only named input can now be stated directly as a
lag-correlation estimate for `mulConvPow (jacobiWeight χ) 2`, rather than as a special case of
the general sextic variety package.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R42CubeLagInput

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The zero-twist base weight is the Jacobi base weight. -/
theorem twistedWeight_zero_eq_jacobiWeight (hfam : SubgroupDualFamily G m lam) :
    twistedWeight χ lam 0 = jacobiWeight χ := by
  funext z
  by_cases hz : z = 0
  · simp [twistedWeight, jacobiWeight, hz]
  · simp [twistedWeight, hfam.triv_on_units z hz]

/-- The cube shape `(0,0)` in the sextic input is exactly `f₀^{⊛3}`. -/
theorem tripleTwistWeight_zero_zero_eq_mulConvPow_two
    (hfam : SubgroupDualFamily G m lam) :
    tripleTwistWeight χ lam 0 0 = mulConvPow (jacobiWeight χ) 2 := by
  simp [tripleTwistWeight, mulConvPow, twistedWeight_zero_eq_jacobiWeight hfam]

/-- Concrete cube lag input: a lag-correlation bound for the `J³` convolution weight. -/
def CubeLagInput (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F)
    (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ t : ZMod m, t ≠ 0 →
    ‖∑ w : F, mulConvPow (jacobiWeight χ) 2 (u * w)
        * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖
      ≤ C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2

/-- The concrete `J³` lag input supplies the cube-only sextic input of round 41. -/
theorem cubeSexticVarietyInput_of_cubeLagInput
    (hfam : SubgroupDualFamily G m lam) {C : ℝ}
    (hcube : CubeLagInput χ lam G C) :
    CubeSexticVarietyInput χ lam G C := by
  intro u hu t ht
  rw [tripleTwistWeight_zero_zero_eq_mulConvPow_two (χ := χ) hfam]
  exact hcube u hu t ht

/-- The split sextic consumer with the cube side stated as the concrete `J³` lag input. -/
theorem sextic_correlation_bound_of_generic_cubeLag
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ} (hCg : 0 ≤ Cgeneric) (hCc : 0 ≤ Ccube)
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    {a b a' b' t : ZMod m} (ht : t ≠ 0) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * (G.card : ℝ) * max Cgeneric Ccube
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
  sextic_correlation_bound_of_generic_cube hfam hgrp hCg hCc hgeneric
    (cubeSexticVarietyInput_of_cubeLagInput hfam hcube) ht

/-- The split sextic input with the cube side stated as concrete `J³` lag control, plus an
explicit zero-lag budget, supplies the all-lag R37 `SexticCorrelationBound` interface. -/
theorem sexticCorrelationBound_of_generic_cubeLag_and_zeroLag
    (hfam : SubgroupDualFamily G m lam)
    {Cgeneric Ccube B : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hzero : ∀ a b a' b' : ZMod m,
      ‖∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖ ≤ B)
    (hbudget :
      (G.card : ℝ) * (max Cgeneric Ccube * Real.sqrt (Fintype.card F)
        * (Fintype.card F : ℝ) ^ 2) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_generic_cube_and_zeroLag hgeneric
    (cubeSexticVarietyInput_of_cubeLagInput hfam hcube) hzero hbudget

#print axioms ArkLib.ProximityGap.Frontier.R42CubeLagInput.twistedWeight_zero_eq_jacobiWeight
#print axioms
  ArkLib.ProximityGap.Frontier.R42CubeLagInput.tripleTwistWeight_zero_zero_eq_mulConvPow_two
#print axioms ArkLib.ProximityGap.Frontier.R42CubeLagInput.cubeSexticVarietyInput_of_cubeLagInput
#print axioms
  ArkLib.ProximityGap.Frontier.R42CubeLagInput.sextic_correlation_bound_of_generic_cubeLag
#print axioms
  ArkLib.ProximityGap.Frontier.R42CubeLagInput.sexticCorrelationBound_of_generic_cubeLag_and_zeroLag

end ArkLib.ProximityGap.Frontier.R42CubeLagInput
