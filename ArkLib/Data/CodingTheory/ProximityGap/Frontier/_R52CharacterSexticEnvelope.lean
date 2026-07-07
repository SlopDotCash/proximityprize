/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R51PrimitiveSexticEnvelope

/-!
# LANE B2 (#466 round 52): character envelopes for the sextic zero-lag adapter

Round 51 reduced the sextic zero-lag bookkeeping to a `jacobiWeight` envelope and a λ-family
envelope.  This brick replaces the former by the even more primitive envelope on `χ` itself:
since `jacobiWeight χ z` is either zero or `χ (1 - z)`, a uniform bound on `χ` bounds the
Jacobi base weight.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- A pointwise envelope for `χ` bounds the zero-patched Jacobi base weight. -/
theorem norm_jacobiWeight_le_of_characterEnvelope
    {A : ℝ} (hA0 : 0 ≤ A) (hχ : ∀ x : F, ‖χ x‖ ≤ A) (z : F) :
    ‖jacobiWeight χ z‖ ≤ A := by
  by_cases hz : z = 0
  · unfold jacobiWeight
    rw [if_pos hz]
    simpa using hA0
  · unfold jacobiWeight
    rw [if_neg hz]
    exact hχ (1 - z)

/-- R51 with the Jacobi-weight envelope supplied from a primitive character envelope. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelopes
    {C A L B : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L)
    (hweil : SexticVarietyInput χ lam G C)
    (hχ : ∀ x : F, ‖χ x‖ ≤ A)
    (hL : ∀ t : ZMod m, ∀ z : F, ‖lam t z‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * (A * L) ^ 3) ^ 2 * L))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_primitiveEnvelopes
    hA0 hL0 hweil
    (norm_jacobiWeight_le_of_characterEnvelope hA0 hχ)
    hL
    hbudget

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope.norm_jacobiWeight_le_of_characterEnvelope
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_characterEnvelopes

end ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope
