/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R40CubeClassExact

/-!
# LANE B2 (#466 round 41): split the final sextic input into cube and generic shapes

Round 39 found the largest calibrated instances of `SexticVarietyInput` occur at the
degenerate cube shape `(a,b,a',b') = (0,0,0,0)`.  Round 40 proved that cube class is itself a
landed weighted-lag correlation identity.  This file records the proof-plumbing consequence:

* `GenericSexticVarietyInput` controls all non-cube shapes;
* `CubeSexticVarietyInput` controls only the cube shape;
* together they imply the original all-shapes `SexticVarietyInput`, with constant
  `max Cgeneric Ccube`, and hence the existing sextic correlation bound.

This makes the final named input thinner: the generic Katz/Deligne hypothesis no longer has to
cover the stress-extremal cube class.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R41SexticInputSplit

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R40CubeClassExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The degenerate cube shape found by the stress probe: correlation of `J^3` with itself. -/
def IsCubeSexticShape (a b a' b' : ZMod m) : Prop :=
  a = 0 ∧ b = 0 ∧ a' = 0 ∧ b' = 0

/-- Generic sextic input: the R38 bound only away from the cube shape. -/
def GenericSexticVarietyInput (χ : F → ℂ) (lam : ZMod m → F → ℂ)
    (G : Finset F) (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ a b a' b' t : ZMod m, t ≠ 0 → ¬ IsCubeSexticShape a b a' b' →
    ‖∑ w : F, tripleTwistWeight χ lam a b (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam t w‖
      ≤ C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2

/-- Cube-only sextic input: the same bound restricted to `(a,b,a',b') = (0,0,0,0)`.
Round 40 identifies this class with the weighted lag correlation of `J^3`. -/
def CubeSexticVarietyInput (χ : F → ℂ) (lam : ZMod m → F → ℂ)
    (G : Finset F) (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ t : ZMod m, t ≠ 0 →
    ‖∑ w : F, tripleTwistWeight χ lam 0 0 (u * w)
        * (starRingEnd ℂ) (tripleTwistWeight χ lam 0 0 w) * lam t w‖
      ≤ C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2

/-- Cube + generic inputs recover the original all-shapes R38 input, with the maximum constant. -/
theorem sexticVarietyInput_of_generic_cube
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeSexticVarietyInput χ lam G Ccube) :
    SexticVarietyInput χ lam G (max Cgeneric Ccube) := by
  intro u hu a b a' b' t ht
  by_cases hshape : IsCubeSexticShape a b a' b'
  · rcases hshape with ⟨ha, hb, ha', hb'⟩
    subst ha
    subst hb
    subst ha'
    subst hb'
    have h := hcube u hu t ht
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card F) := by positivity
    have hpow_nonneg : 0 ≤ (Fintype.card F : ℝ) ^ 2 := by positivity
    exact le_trans h (by
      have hle : Ccube ≤ max Cgeneric Ccube := le_max_right _ _
      have h1 : Ccube * Real.sqrt (Fintype.card F)
          ≤ max Cgeneric Ccube * Real.sqrt (Fintype.card F) :=
        mul_le_mul_of_nonneg_right hle hsqrt_nonneg
      exact mul_le_mul_of_nonneg_right h1 hpow_nonneg)
  · have h := hgeneric u hu a b a' b' t ht hshape
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card F) := by positivity
    have hpow_nonneg : 0 ≤ (Fintype.card F : ℝ) ^ 2 := by positivity
    exact le_trans h (by
      have hle : Cgeneric ≤ max Cgeneric Ccube := le_max_left _ _
      have h1 : Cgeneric * Real.sqrt (Fintype.card F)
          ≤ max Cgeneric Ccube * Real.sqrt (Fintype.card F) :=
        mul_le_mul_of_nonneg_right hle hsqrt_nonneg
      exact mul_le_mul_of_nonneg_right h1 hpow_nonneg)

/-- The split form of the R38 sextic correlation consumer. -/
theorem sextic_correlation_bound_of_generic_cube
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {Cgeneric Ccube : ℝ} (hCg : 0 ≤ Cgeneric) (hCc : 0 ≤ Ccube)
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeSexticVarietyInput χ lam G Ccube)
    {a b a' b' t : ZMod m} (ht : t ≠ 0) :
    ‖∑ j : ZMod m,
        (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
          * jacobiCoeff χ lam ((j + t) + b))
        * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
          * jacobiCoeff χ lam (j + b'))‖
      ≤ (m : ℝ) * (G.card : ℝ) * max Cgeneric Ccube
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
  sextic_correlation_bound hfam hgrp (by
    rcases le_total Cgeneric Ccube with hle | hle
    · rw [max_eq_right hle]
      exact hCc
    · rw [max_eq_left hle]
      exact hCg)
    (sexticVarietyInput_of_generic_cube hgeneric hcube) ht

/-- The split generic/cube input, plus an explicit zero-lag budget, supplies the all-lag
R37 `SexticCorrelationBound` interface. -/
theorem sexticCorrelationBound_of_generic_cube_and_zeroLag
    {Cgeneric Ccube B : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeSexticVarietyInput χ lam G Ccube)
    (hzero : ∀ a b a' b' : ZMod m,
      ‖∑ u ∈ G, ∑ w : F,
          tripleTwistWeight χ lam a b (u * w)
            * (starRingEnd ℂ) (tripleTwistWeight χ lam a' b' w) * lam 0 w‖ ≤ B)
    (hbudget :
      (G.card : ℝ) * (max Cgeneric Ccube * Real.sqrt (Fintype.card F)
        * (Fintype.card F : ℝ) ^ 2) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_zeroLag
    (C := max Cgeneric Ccube) (B := B)
    (sexticVarietyInput_of_generic_cube hgeneric hcube) hzero hbudget

set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R41SexticInputSplit.sexticVarietyInput_of_generic_cube
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R41SexticInputSplit.sextic_correlation_bound_of_generic_cube
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R41SexticInputSplit.sexticCorrelationBound_of_generic_cube_and_zeroLag

end ArkLib.ProximityGap.Frontier.R41SexticInputSplit
