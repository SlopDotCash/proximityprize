/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R42CubeLagInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R54CharacterUnitSexticEnvelope

/-!
# LANE B2 (#466 round 57): split cube/generic sextic input at the unit budget

Rounds 41--42 split the R38 nonzero-lag sextic variety input into a generic part and the
stress-extremal cube lag `J³` part.  This file composes that split with the unit-character
zero-lag envelope from rounds 49--54.

The result is the same all-lag R37 `SexticCorrelationBound` interface, but the nonzero-lag
mathematical obligation is now:

* generic non-cube sextic cancellation, and
* concrete cube-lag cancellation for `f₀^{⊛3}`.

The zero-lag slice is discharged from normalized character and dual-family hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope
open ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope
open ArkLib.ProximityGap.Frontier.R51PrimitiveSexticEnvelope
open ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope
open ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope
open ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The all-lag budget for the split generic/cube-lag sextic input under unit character and
dual-family envelopes. -/
noncomputable def splitCubeLagUnitBudget (G : Finset F) (Cgeneric Ccube : ℝ) : ℝ :=
  max
    ((G.card : ℝ) * (max Cgeneric Ccube * Real.sqrt (Fintype.card F)
      * (Fintype.card F : ℝ) ^ 2))
    ((G.card : ℝ) * ((Fintype.card F : ℝ)
      * ((Fintype.card F : ℝ) ^ 2) ^ 2))

/-- Unit character and dual-family hypotheses bound every triple twisted weight by `q²`. -/
theorem norm_tripleTwistWeight_le_card_sq_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (a b : ZMod m) (z : F) :
    ‖tripleTwistWeight χ lam a b z‖ ≤ (Fintype.card F : ℝ) ^ 2 := by
  have hchar : ∀ x : F, ‖χ x‖ ≤ (1 : ℝ) :=
    norm_character_le_one hχ hχ1
  have hA : ∀ z : F, ‖jacobiWeight χ z‖ ≤ (1 : ℝ) :=
    norm_jacobiWeight_le_of_characterEnvelope (χ := χ) (A := (1 : ℝ)) (by norm_num) hchar
  have hL : ∀ t : ZMod m, ∀ z : F, ‖lam t z‖ ≤ (1 : ℝ) :=
    norm_lam_le_one_of_dualFamily hfam hgrp
  have hW : ∀ t : ZMod m, ∀ z : F, ‖twistedWeight χ lam t z‖ ≤ (1 : ℝ) := by
    intro t z
    simpa using
      (norm_twistedWeight_le_mul (χ := χ) (lam := lam) (A := (1 : ℝ)) (L := (1 : ℝ))
        (by norm_num) hA hL t z)
  simpa using
    (norm_tripleTwistWeight_le_card_sq_mul_cube
      (χ := χ) (lam := lam) (W := (1 : ℝ)) (by norm_num) hW a b z)

/-- Generic non-cube sextic input plus concrete cube-lag input supplies the all-lag R37
`SexticCorrelationBound` at the explicit split unit budget. -/
theorem sexticCorrelationBound_of_generic_cubeLag_unitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube) :
    SexticCorrelationBound χ lam G
      (splitCubeLagUnitBudget (F := F) G Cgeneric Ccube) := by
  refine sexticCorrelationBound_of_generic_cubeLag_and_zeroLag
    (χ := χ) (lam := lam) (G := G) hfam hgeneric hcube ?_ ?_
  · intro a b a' b'
    have hzero := sextic_zeroLag_bound_of_tripleEnvelope
      (χ := χ) (lam := lam) (G := G)
      (T := (Fintype.card F : ℝ) ^ 2) (L := (1 : ℝ))
      (by positivity)
      (norm_tripleTwistWeight_le_card_sq_of_unitCharacters hχ hχ1 hfam hgrp)
      (fun w => by simpa using norm_lam_le_one_of_dualFamily hfam hgrp (0 : ZMod m) w)
      a b a' b'
    calc
      ‖∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖
          ≤ (G.card : ℝ)
              * ((Fintype.card F : ℝ)
                * (((Fintype.card F : ℝ) ^ 2) ^ 2 * (1 : ℝ))) := hzero
      _ = (G.card : ℝ)
              * ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) ^ 2) ^ 2) := by ring
      _ ≤ splitCubeLagUnitBudget (F := F) G Cgeneric Ccube := by
          unfold splitCubeLagUnitBudget
          exact le_max_right _ _
  · unfold splitCubeLagUnitBudget
    exact le_max_left _ _

/-- Pointwise six-`J` bound from the split generic/cube-lag input at the explicit unit budget. -/
theorem sextic_correlation_bound_of_generic_cubeLag_unitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * splitCubeLagUnitBudget (F := F) G Cgeneric Ccube :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_cubeLag_unitBudget hχ hχ1 hfam hgrp hgeneric hcube)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy from the split generic/cube-lag input at the explicit
unit budget. -/
theorem sextic_correlation_energy_bound_of_generic_cubeLag_unitBudget
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * splitCubeLagUnitBudget (F := F) G Cgeneric Ccube) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_generic_cubeLag_unitBudget hχ hχ1 hfam hgrp hgeneric hcube)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget.norm_tripleTwistWeight_le_card_sq_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget.sexticCorrelationBound_of_generic_cubeLag_unitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget.sextic_correlation_bound_of_generic_cubeLag_unitBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget.sextic_correlation_energy_bound_of_generic_cubeLag_unitBudget

end ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget
