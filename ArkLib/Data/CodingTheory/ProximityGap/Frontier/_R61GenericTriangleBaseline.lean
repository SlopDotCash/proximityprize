/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R57SplitCubeLagUnitBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R60GenericOnlyAfterCubeTriangle

/-!
# LANE B2 (#466 round 61): triangle-inequality baseline for the generic sextic input

Round 60 leaves only the generic non-cube sextic input in the split route once the cube side is
discharged at triangle scale.  This file proves the matching no-cancellation baseline for the
generic input itself: under normalized character and dual-family hypotheses, every generic fiber
sum satisfies the `GenericSexticVarietyInput` interface with constant `q³`.

Composed with round 60, this gives a fully discharged coarse all-lag sextic interface at
`normalizedUnitSexticBudget G q³`.  The prize problem is exactly the missing improvement from
this polynomial triangle constant to an absolute Deligne/Katz constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R56SexticBudgetNormalization
open ArkLib.ProximityGap.Frontier.R57SplitCubeLagUnitBudget
open ArkLib.ProximityGap.Frontier.R53DualFamilySexticEnvelope
open ArkLib.ProximityGap.Frontier.R60GenericOnlyAfterCubeTriangle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The elementary triangle bound for each generic sextic fiber sum.  The proof does not use
genericity; it records the coarse no-cancellation scale for all shapes. -/
theorem norm_genericSextic_sum_le_card_pow_five_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (u : F) (a b a' b' t : ZMod m) :
    ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
      ≤ (Fintype.card F : ℝ) ^ 5 := by
  classical
  have hterm : ∀ w : F,
      ‖tripleTwistWeight χ lam a b (u * w)
          * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
        ≤ ((Fintype.card F : ℝ) ^ 2) ^ 2 * (1 : ℝ) := by
    intro w
    rw [norm_mul, norm_mul]
    have hstar :
        ‖(starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w)‖
          = ‖tripleTwistWeight χ lam a' b' w‖ := by
      simp
    rw [hstar]
    have hmul :
        ‖tripleTwistWeight χ lam a b (u * w)‖
            * ‖tripleTwistWeight χ lam a' b' w‖
          ≤ (Fintype.card F : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2 :=
      mul_le_mul
        (norm_tripleTwistWeight_le_card_sq_of_unitCharacters hχ hχ1 hfam hgrp a b (u * w))
        (norm_tripleTwistWeight_le_card_sq_of_unitCharacters hχ hχ1 hfam hgrp a' b' w)
        (norm_nonneg _)
        (by positivity)
    have hmulL :
        ‖tripleTwistWeight χ lam a b (u * w)‖
            * ‖tripleTwistWeight χ lam a' b' w‖ * ‖lam t w‖
          ≤ ((Fintype.card F : ℝ) ^ 2 * (Fintype.card F : ℝ) ^ 2) * (1 : ℝ) :=
      mul_le_mul hmul (norm_lam_le_one_of_dualFamily hfam hgrp t w)
        (norm_nonneg _) (by positivity)
    exact hmulL.trans_eq (by ring)
  calc
    ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
        ≤ ∑ w : F,
            ‖tripleTwistWeight χ lam a b (u * w)
              * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _w : F, ((Fintype.card F : ℝ) ^ 2) ^ 2 * (1 : ℝ) :=
          Finset.sum_le_sum (fun w _ => hterm w)
    _ = (Fintype.card F : ℝ) ^ 5 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp
          ring

/-- Pure triangle inequality supplies the generic non-cube input with coarse constant `q³`. -/
theorem genericSexticVarietyInput_triangle_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) :
    GenericSexticVarietyInput χ lam G ((Fintype.card F : ℝ) ^ 3) := by
  intro u _hu a b a' b' t _ht _hshape
  have hbase := norm_genericSextic_sum_le_card_pow_five_of_unitCharacters
    hχ hχ1 hfam hgrp u a b a' b' t
  have hcard_one : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    have hlt : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
    exact_mod_cast le_of_lt hlt
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    exact Real.le_sqrt_of_sq_le (by simpa using hcard_one)
  have hnonneg : 0 ≤ (Fintype.card F : ℝ) ^ 5 := by positivity
  calc
    ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
        ≤ (Fintype.card F : ℝ) ^ 5 := hbase
    _ = (Fintype.card F : ℝ) ^ 5 * (1 : ℝ) := by ring
    _ ≤ (Fintype.card F : ℝ) ^ 5 * Real.sqrt (Fintype.card F) :=
        mul_le_mul_of_nonneg_left hsqrt_one hnonneg
    _ = (Fintype.card F : ℝ) ^ 3 * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2 := by ring

/-- Fully discharged coarse all-lag sextic interface at triangle scale. -/
theorem sexticCorrelationBound_triangle_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) :
    SexticCorrelationBound χ lam G
      (normalizedUnitSexticBudget (F := F) G ((Fintype.card F : ℝ) ^ 3)) := by
  simpa using
    (sexticCorrelationBound_of_generic_unitCharacters_cubeTriangle
      (F := F) (m := m) (lam := lam) (G := G) (χ := χ)
      hχ hχ1 hfam hgrp
      (genericSexticVarietyInput_triangle_of_unitCharacters hχ hχ1 hfam hgrp))

/-- Pointwise six-`J` bound at the fully discharged triangle scale. -/
theorem sextic_correlation_bound_triangle_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (a b a' b' t : ZMod m) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * normalizedUnitSexticBudget (F := F) G
          ((Fintype.card F : ℝ) ^ 3) :=
  sextic_correlation_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_triangle_of_unitCharacters hχ hχ1 hfam hgrp)
    a b a' b' t

/-- Aggregate all-lag six-`J` energy at the fully discharged triangle scale. -/
theorem sextic_correlation_energy_bound_triangle_of_unitCharacters
    (hχ : IsMulCharC χ) (hχ1 : χ 1 = 1)
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * normalizedUnitSexticBudget (F := F) G
            ((Fintype.card F : ℝ) ^ 3)) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_triangle_of_unitCharacters hχ hχ1 hfam hgrp)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline.norm_genericSextic_sum_le_card_pow_five_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline.genericSexticVarietyInput_triangle_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline.sexticCorrelationBound_triangle_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline.sextic_correlation_bound_triangle_of_unitCharacters
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline.sextic_correlation_energy_bound_triangle_of_unitCharacters

end ArkLib.ProximityGap.Frontier.R61GenericTriangleBaseline
