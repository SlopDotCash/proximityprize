/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R49SexticZeroLagEnvelope

/-!
# LANE B2 (#466 round 50): triple twisted envelopes from base twisted envelopes

Round 49 reduced the sextic zero-lag diagonal to a pointwise envelope for
`tripleTwistWeight`.  This brick pushes that envelope one level lower: a uniform bound `W`
for every twisted base weight gives

`‖tripleTwistWeight χ lam a b z‖ ≤ q² W³`.

The proof is deliberately elementary: the multiplicative convolution sum has at most `q`
terms, so envelopes multiply with one `q` factor per convolution.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R35TransformRingHom
open ArkLib.ProximityGap.Frontier.R37SexticExact
open ArkLib.ProximityGap.Frontier.R38SexticVarietyInput
open ArkLib.ProximityGap.Frontier.R49SexticZeroLagEnvelope

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- A pointwise envelope for two weights gives a pointwise envelope for their multiplicative
convolution, losing only the ambient field cardinality. -/
theorem norm_mulConv_le_card_mul
    (f g : F → ℂ) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hf : ∀ z : F, ‖f z‖ ≤ A) (hg : ∀ z : F, ‖g z‖ ≤ B) (v : F) :
    ‖mulConv f g v‖ ≤ (Fintype.card F : ℝ) * (A * B) := by
  classical
  calc
    ‖mulConv f g v‖
        ≤ ∑ z ∈ (Finset.univ : Finset F).erase 0, ‖f z * g (z⁻¹ * v)‖ := by
          unfold mulConv
          exact norm_sum_le _ _
    _ ≤ ∑ _z ∈ (Finset.univ : Finset F).erase 0, A * B := by
          refine Finset.sum_le_sum (fun z _hz => ?_)
          rw [norm_mul]
          exact mul_le_mul (hf z) (hg (z⁻¹ * v)) (norm_nonneg _) hA0
    _ ≤ ∑ _z : F, A * B := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro z hz; exact Finset.mem_univ z)
            (by intro z _hz hnot; exact mul_nonneg hA0 hB0)
    _ = (Fintype.card F : ℝ) * (A * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp

/-- A uniform twisted-base envelope gives the triple twisted-weight envelope used by R49. -/
theorem norm_tripleTwistWeight_le_card_sq_mul_cube
    {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ t : ZMod m, ∀ z : F, ‖twistedWeight χ lam t z‖ ≤ W)
    (a b : ZMod m) (z : F) :
    ‖tripleTwistWeight χ lam a b z‖
      ≤ (Fintype.card F : ℝ) ^ 2 * W ^ 3 := by
  classical
  have hconv : ∀ v : F,
      ‖mulConv (twistedWeight χ lam 0) (twistedWeight χ lam a) v‖
        ≤ (Fintype.card F : ℝ) * (W * W) :=
    norm_mulConv_le_card_mul (twistedWeight χ lam 0) (twistedWeight χ lam a)
      hW0 hW0 (hW 0) (hW a)
  unfold tripleTwistWeight
  have hmain := norm_mulConv_le_card_mul
    (mulConv (twistedWeight χ lam 0) (twistedWeight χ lam a))
    (twistedWeight χ lam b)
    (by positivity)
    hW0
    hconv
    (hW b)
    z
  calc
    ‖mulConv (mulConv (twistedWeight χ lam 0) (twistedWeight χ lam a))
        (twistedWeight χ lam b) z‖
        ≤ (Fintype.card F : ℝ) * (((Fintype.card F : ℝ) * (W * W)) * W) := hmain
    _ = (Fintype.card F : ℝ) ^ 2 * W ^ 3 := by ring

/-- R49 with the triple envelope supplied from a base twisted-weight envelope. -/
theorem sexticCorrelationBound_of_sexticVarietyInput_and_baseEnvelopes
    {C W L B : ℝ} (hW0 : 0 ≤ W)
    (hweil : SexticVarietyInput χ lam G C)
    (hW : ∀ t : ZMod m, ∀ z : F, ‖twistedWeight χ lam t z‖ ≤ W)
    (hL : ∀ w : F, ‖lam 0 w‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * W ^ 3) ^ 2 * L))) ≤ B) :
    SexticCorrelationBound χ lam G B :=
  sexticCorrelationBound_of_sexticVarietyInput_and_envelopes
    (T := (Fintype.card F : ℝ) ^ 2 * W ^ 3)
    (L := L)
    (hT0 := by positivity)
    hweil
    (fun a b z => norm_tripleTwistWeight_le_card_sq_mul_cube hW0 hW a b z)
    hL
    hbudget

/-- Direct all-lag sextic-energy consumer from the final variety input plus elementary
twisted-base envelopes.  This composes the R50 envelope bookkeeping with the R37 energy
summation, so a future Katz/Deligne proof can feed the energy surface in one step. -/
theorem sextic_correlation_energy_bound_of_sexticVarietyInput_and_baseEnvelopes
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {C W L B : ℝ} (hW0 : 0 ≤ W)
    (hweil : SexticVarietyInput χ lam G C)
    (hW : ∀ t : ZMod m, ∀ z : F, ‖twistedWeight χ lam t z‖ ≤ W)
    (hL : ∀ w : F, ‖lam 0 w‖ ≤ L)
    (hbudget :
      max
        ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ) ^ 2))
        ((G.card : ℝ) * ((Fintype.card F : ℝ)
          * (((Fintype.card F : ℝ) ^ 2 * W ^ 3) ^ 2 * L))) ≤ B) :
    ∑ a : ZMod m, ∑ b : ZMod m, ∑ a' : ZMod m, ∑ b' : ZMod m, ∑ t : ZMod m,
        ‖∑ j : ZMod m,
          (jacobiCoeff χ lam (j + t) * jacobiCoeff χ lam ((j + t) + a)
            * jacobiCoeff χ lam ((j + t) + b))
          * (starRingEnd ℂ) (jacobiCoeff χ lam j * jacobiCoeff χ lam (j + a')
            * jacobiCoeff χ lam (j + b'))‖ ^ 2
      ≤ ((m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * B) ^ 2) :=
  sextic_correlation_energy_bound_of_sexticCorrelationBound hfam hgrp
    (sexticCorrelationBound_of_sexticVarietyInput_and_baseEnvelopes
      hW0 hweil hW hL hbudget)

set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope.norm_mulConv_le_card_mul
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope.norm_tripleTwistWeight_le_card_sq_mul_cube
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope.sexticCorrelationBound_of_sexticVarietyInput_and_baseEnvelopes
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope.sextic_correlation_energy_bound_of_sexticVarietyInput_and_baseEnvelopes

end ArkLib.ProximityGap.Frontier.R50TripleTwistEnvelope
