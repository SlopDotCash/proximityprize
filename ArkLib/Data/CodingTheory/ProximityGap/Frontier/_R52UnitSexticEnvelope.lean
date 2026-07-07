/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R51PrimitiveSexticEnvelope

/-!
# LANE B2 (#466 round 52): unit primitive envelopes for the sextic zero-lag adapter

Round 51 reduced the sextic zero-lag envelope to primitive pointwise bounds for the Jacobi
base weight and the dual-family characters.  Both primitive bounds are unit bounds in the
actual character package:

* `‖χ(1-z)‖ ≤ 1`, with the zero at `z = 1` handled by `χ 0 = 0`;
* `‖λ_t z‖ ≤ 1`, with the zero at `z = 0` handled by `λ_t 0 = 0`.

This packages the elementary unit envelopes into the R51 all-lag sextic consumer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R52UnitSexticEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The Jacobi base weight has pointwise norm at most one for a normalized multiplicative
character. -/
theorem norm_jacobiWeight_le_one (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1) (z : F) :
    ‖jacobiWeight χ z‖ ≤ 1 := by
  by_cases hz0 : z = 0
  · simp [jacobiWeight, hz0]
  · by_cases hz : 1 - z = 0
    · have hz1 : z = 1 := by linear_combination -hz
      simp [jacobiWeight, hz1, hχ.map_zero]
    · rw [jacobiWeight, if_neg hz0]
      exact le_of_eq (norm_chi_eq_one hχ hχ1 hz)

/-- Every dual-family character has pointwise norm at most one, including the zero point. -/
theorem norm_lam_le_one (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (t : ZMod m) (z : F) :
    ‖lam t z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hfam.map_zero t, hz]
  · exact le_of_eq (hgrp.norm_one t z hz)

/-- R51 with the primitive envelopes discharged by unit character bounds. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_unitEnvelopes
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C B : ℝ}
    (hweil : SexticVarietyInput χ lam G C)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * ((1 : ℝ) * 1) ^ 3) ^ 2 * 1))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_primitiveEnvelopes
    (A := 1) (L := 1)
    (by norm_num) (by norm_num)
    hweil
    (norm_jacobiWeight_le_one hχ hχ1)
    (norm_lam_le_one hfam hgrp)
    hbudget

set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R52UnitSexticEnvelope.norm_jacobiWeight_le_one
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R52UnitSexticEnvelope.norm_lam_le_one
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R52UnitSexticEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_unitEnvelopes

end ArkLib.ProximityGap.Frontier.R52UnitSexticEnvelope
