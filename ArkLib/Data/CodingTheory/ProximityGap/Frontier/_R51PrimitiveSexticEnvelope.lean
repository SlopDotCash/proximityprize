/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R50TripleTwistEnvelope

/-!
# LANE B2 (#466 round 51): primitive envelopes for the sextic zero-lag adapter

Round 50 reduced the R49 triple-weight hypothesis to a uniform envelope for the twisted base
weights `f₀ · λ_t`.  This file pushes once more to primitive data: an envelope for the Jacobi
base weight and an envelope for the λ-family imply the twisted envelope, hence the all-lag
R37 `SexticCorrelationBound` consumer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Separate envelopes for the Jacobi base weight and λ-family give the twisted-base envelope. -/
theorem norm_twistedWeight_le_mul
    {A L : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ z : F, ‖jacobiWeight χ z‖ ≤ A)
    (hL : ∀ t : ZMod m, ∀ z : F, ‖lam t z‖ ≤ L)
    (t : ZMod m) (z : F) :
    ‖twistedWeight χ lam t z‖ ≤ A * L := by
  rw [twistedWeight, norm_mul]
  exact mul_le_mul (hA z) (hL t z) (norm_nonneg _) hA0

/-- R50 with the twisted-base envelope supplied from primitive `jacobiWeight` and λ envelopes. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_primitiveEnvelopes
    {C A L B : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L)
    (hweil : SexticVarietyInput χ lam G C)
    (hA : ∀ z : F, ‖jacobiWeight χ z‖ ≤ A)
    (hL : ∀ t : ZMod m, ∀ z : F, ‖lam t z‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * (A * L) ^ 3) ^ 2 * L))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_baseEnvelopes
    (W := A * L)
    (L := L)
    (hW0 := mul_nonneg hA0 hL0)
    hweil
    (fun t z => norm_twistedWeight_le_mul hA0 hA hL t z)
    (hL 0)
    hbudget

/-- Aggregate all-lag six-J energy from primitive Jacobi-weight and λ-family envelopes. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_and_primitiveEnvelopes
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C A L B : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L)
    (hweil : SexticVarietyInput χ lam G C)
    (hA : ∀ z : F, ‖jacobiWeight χ z‖ ≤ A)
    (hL : ∀ t : ZMod m, ∀ z : F, ‖lam t z‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * (A * L) ^ 3) ^ 2 * L))) ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_and_primitiveEnvelopes
      hA0 hL0 hweil hA hL hbudget)

set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope.norm_twistedWeight_le_mul
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_primitiveEnvelopes
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope.sextic_correlation_energy_bound_of_sexticVarietyInput_and_primitiveEnvelopes

end ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope
