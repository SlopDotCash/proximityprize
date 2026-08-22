/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R366CenteredRelationAnomaly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R313LocalShadowCollisionLoad

/-!
# R367: the relation anomaly is a signed discrepancy over all shadow pairs

Raw kernel counting keeps only colliding pairs and is necessarily too large after the DC
crossover.  The centered object has cancellation: a colliding pair contributes `(q-1)` times its
weight, while a non-colliding pair contributes minus its weight.  This file proves that this
signed pair sum is exactly R366's `relationAnomaly`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-- Total weighted mass of all ordered distinct shadow-key pairs. -/
noncomputable def allShadowOffDiagMass (n m r : ℕ) : ℕ :=
  ∑ p ∈ (keysR n m r).offDiag, NR n m r p.1 * NR n m r p.2

/-- The diagonal shadow energy plus all off-diagonal pair mass is the total tuple-pair mass. -/
theorem shadowEnergy_add_allShadowOffDiagMass_eq_pow (n m r : ℕ) :
    shadowEnergy n m r + allShadowOffDiagMass n m r = n ^ (2 * r) := by
  have h := sum_sq_eq_sum_sq_add_offDiag (keysR n m r) (NR n m r)
  rw [sum_NR_keysR] at h
  unfold shadowEnergy allShadowOffDiagMass
  rw [← h]
  rw [pow_two, ← pow_add, two_mul]

/-- A generic indicator-centering identity on a finite weighted set. -/
theorem sum_indicator_discrepancy
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → Prop) [DecidablePred P]
    (w : α → ℝ) (q : ℝ) :
    (∑ x ∈ S, w x * (q * (if P x then 1 else 0) - 1)) =
      q * (∑ x ∈ S.filter P, w x) - ∑ x ∈ S, w x := by
  calc
    (∑ x ∈ S, w x * (q * (if P x then 1 else 0) - 1)) =
        ∑ x ∈ S, (q * (if P x then w x else 0) - w x) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hP : P x <;> simp [hP] <;> ring
    _ = (∑ x ∈ S, q * (if P x then w x else 0)) - ∑ x ∈ S, w x := by
      rw [Finset.sum_sub_distrib]
    _ = q * (∑ x ∈ S.filter P, w x) - ∑ x ∈ S, w x := by
      rw [Finset.mul_sum, Finset.sum_filter]
      congr 2
      funext x
      by_cases hP : P x <;> simp [hP]

/-- Signed discrepancy of the evaluation map on weighted off-diagonal shadow pairs. -/
noncomputable def signedShadowPairDiscrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) : ℝ :=
  ∑ p ∈ (keysR n m r).offDiag,
    (NR n m r p.1 * NR n m r p.2 : ℝ) *
      ((Fintype.card F : ℝ) *
        (if evalVec g m p.1 = evalVec g m p.2 then 1 else 0) - 1)

/-- **Exact signed form of the deep wall.** The pair discrepancy equals the centered relation
anomaly: positive colliding mass and negative non-colliding mass cancel at the uniform scale. -/
theorem signedShadowPairDiscrepancy_eq_relationAnomaly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) :
    signedShadowPairDiscrepancy g n m r = relationAnomaly g n m r := by
  classical
  rw [signedShadowPairDiscrepancy,
    sum_indicator_discrepancy (keysR n m r).offDiag
      (fun p => evalVec g m p.1 = evalVec g m p.2)
      (fun p => (NR n m r p.1 * NR n m r p.2 : ℝ)) (Fintype.card F : ℝ)]
  have hcoll := shadowCollisionMass_eq_sum_pairs g n m r
  have hoff := shadowEnergy_add_allShadowOffDiagMass_eq_pow n m r
  unfold shadowCollisionPairs at hcoll
  have hcoll' :
      (∑ p ∈ (keysR n m r).offDiag.filter
          (fun p => evalVec g m p.1 = evalVec g m p.2),
          (NR n m r p.1 * NR n m r p.2 : ℝ)) =
        (shadowCollisionMass g n m r : ℝ) := by
    exact_mod_cast hcoll.symm
  have hoff' :
      (∑ p ∈ (keysR n m r).offDiag,
          NR n m r p.1 * NR n m r p.2 : ℝ) =
        (n : ℝ) ^ (2 * r) - (shadowEnergy n m r : ℝ) := by
    have hoffcast :
        (shadowEnergy n m r : ℝ) + (allShadowOffDiagMass n m r : ℝ) =
          (n : ℝ) ^ (2 * r) := by exact_mod_cast hoff
    have hallcast :
        (allShadowOffDiagMass n m r : ℝ) =
          ∑ p ∈ (keysR n m r).offDiag,
            (NR n m r p.1 * NR n m r p.2 : ℝ) := by
      unfold allShadowOffDiagMass
      push_cast
      rfl
    rw [← hallcast]
    linarith
  rw [hcoll', hoff']
  unfold relationAnomaly
  rfl

end ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy.shadowEnergy_add_allShadowOffDiagMass_eq_pow
#print axioms
  ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy.signedShadowPairDiscrepancy_eq_relationAnomaly
