/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R42CubeLagInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R54CharacterUnitSexticEnvelope

/-!
# LANE B2 (#466 round 59): triangle-inequality baseline for the cube-lag input

The split wall of rounds 57--58 leaves a concrete cube-lag cancellation input for
`f₀^{⊛3}`.  This file proves the fully elementary no-cancellation baseline for that input:
under normalized character and dual-family hypotheses, the cube-lag sum satisfies the
`CubeLagInput` interface with constant `q³`.

This is intentionally not prize-scale cancellation.  It is a formal calibration brick: the
named cube wall asks for an absolute Deligne/Katz constant, while pure triangle inequality
lands at the coarse polynomial constant `q³`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R36JacobiPowers
open ArkLib.ProximityGap.Frontier.R35TransformRingHom
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope
open ArkLib.ProximityGap.Frontier.R52CharacterSexticEnvelope
open ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope
open ArkLib.ProximityGap.Frontier.R54CharacterUnitSexticEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Unit character hypotheses bound the cube convolution weight `f₀^{⊛3}` by `q²`. -/
theorem norm_mulConvPow_two_jacobiWeight_le_card_sq_of_unitCharacter
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1) (z : F) :
    ‖mulConvPow (jacobiWeight χ) 2 z‖ ≤ (Fintype.card F : ℝ) ^ 2 := by
  have hchar : ∀ x : F, ‖χ x‖ ≤ (1 : ℝ) :=
    norm_character_le_one hχ hχ1
  have hbase : ∀ z : F, ‖jacobiWeight χ z‖ ≤ (1 : ℝ) :=
    norm_jacobiWeight_le_of_characterEnvelope (χ := χ) (A := (1 : ℝ)) (by norm_num) hchar
  have hconv : ∀ v : F, ‖mulConv (jacobiWeight χ) (jacobiWeight χ) v‖
      ≤ (Fintype.card F : ℝ) * ((1 : ℝ) * (1 : ℝ)) :=
    norm_mulConv_le_card_mul (jacobiWeight χ) (jacobiWeight χ)
      (by norm_num) (by norm_num) hbase hbase
  unfold mulConvPow
  have hmain := norm_mulConv_le_card_mul
    (mulConv (jacobiWeight χ) (jacobiWeight χ))
    (jacobiWeight χ)
    (by positivity)
    (by norm_num)
    hconv
    hbase
    z
  calc
    ‖mulConv (mulConv (jacobiWeight χ) (jacobiWeight χ)) (jacobiWeight χ) z‖
        ≤ (Fintype.card F : ℝ)
            * (((Fintype.card F : ℝ) * ((1 : ℝ) * (1 : ℝ))) * (1 : ℝ)) := hmain
    _ = (Fintype.card F : ℝ) ^ 2 := by ring

/-- The elementary triangle bound for each cube-lag fiber sum. -/
theorem norm_cubeLag_sum_le_card_pow_five_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (u : F) (t : ZMod m) :
    ‖∑ w : F, mulConvPow (jacobiWeight χ) 2 (u * w)
        * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖
      ≤ (Fintype.card F : ℝ) ^ 5 := by
  classical
  have hterm : ∀ w : F,
      ‖mulConvPow (jacobiWeight χ) 2 (u * w)
          * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖
        ≤ ((Fintype.card F : ℝ) ^ 2) ^ 2 * (1 : ℝ) := by
    intro w
    rw [norm_mul, norm_mul]
    have hstar :
        ‖(starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w)‖
          = ‖mulConvPow (jacobiWeight χ) 2 w‖ := by
      simp
    rw [hstar]
    have hmul :
        ‖mulConvPow (jacobiWeight χ) 2 (u * w)‖
            * ‖mulConvPow (jacobiWeight χ) 2 w‖
          ≤ (Fintype.card F : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 :=
      mul_le_mul
        (norm_mulConvPow_two_jacobiWeight_le_card_sq_of_unitCharacter hχ hχ1 (u * w))
        (norm_mulConvPow_two_jacobiWeight_le_card_sq_of_unitCharacter hχ hχ1 w)
        (norm_nonneg _)
        (by positivity)
    have hmulL :
        ‖mulConvPow (jacobiWeight χ) 2 (u * w)‖
            * ‖mulConvPow (jacobiWeight χ) 2 w‖ * ‖lam t w‖
          ≤ ((Fintype.card F : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2) * (1 : ℝ) :=
      mul_le_mul hmul (norm_lam_le_one_of_dualFamily hfam hgrp t w)
        (norm_nonneg _) (by positivity)
    exact hmulL.trans_eq (by ring)
  calc
    ‖∑ w : F, mulConvPow (jacobiWeight χ) 2 (u * w)
        * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖
        ≤ ∑ w : F,
            ‖mulConvPow (jacobiWeight χ) 2 (u * w)
              * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _w : F, ((Fintype.card F : ℝ) ^ 2) ^ 2 * (1 : ℝ) :=
          Finset.sum_le_sum (fun w _ => hterm w)
    _ = (Fintype.card F : ℝ) ^ 5 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
          ring

/-- Pure triangle inequality supplies `CubeLagInput` with coarse constant `q³`. -/
theorem cubeLagInput_triangle_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) :
    CubeLagInput χ lam G ((Fintype.card F : ℝ) ^ 3) := by
  intro u _hu t _ht
  have hbase := norm_cubeLag_sum_le_card_pow_five_of_unitCharacters hχ hχ1 hfam hgrp u t
  have hcard_one : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    have hlt : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast le_of_lt hlt
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    exact Real.le_sqrt_of_sq_le (by simpa using hcard_one)
  have hnonneg : 0 ≤ (Fintype.card F : ℝ) ^ 5 := by positivity
  calc
    ‖∑ w : F, mulConvPow (jacobiWeight χ) 2 (u * w)
        * (starRingEnd ℂ) (mulConvPow (jacobiWeight χ) 2 w) * lam t w‖
        ≤ (Fintype.card F : ℝ) ^ 5 := hbase
    _ = (Fintype.card F : ℝ) ^ 5 * (1 : ℝ) := by ring
    _ ≤ (Fintype.card F : ℝ) ^ 5 * Real.sqrt (Fintype.card F) :=
        mul_le_mul_of_nonneg_left hsqrt_one hnonneg
    _ = (Fintype.card F : ℝ) ^ 3 * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2 := by ring

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline.norm_mulConvPow_two_jacobiWeight_le_card_sq_of_unitCharacter
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline.norm_cubeLag_sum_le_card_pow_five_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline.cubeLagInput_triangle_of_unitCharacters

end ArkLib.ProximityGap.Frontier.R59CubeLagTriangleBaseline
