/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R367SignedShadowPairDiscrepancy

/-!
# R368: signed discrepancy grouped by every difference vector

The deep centered sum cannot be grouped only over kernel relations: doing so deletes all negative
mass.  Here every realized characteristic-zero difference is retained.  A kernel difference has
coefficient `q-1`; a non-kernel difference has coefficient `-1`.  Grouping the signed pair sum by
these fibers gives the exact lattice-level discrepancy object.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy

/-- Every nonzero difference of two characteristic-zero shadow keys. -/
noncomputable def allShadowDifferences (n m r : ℕ) : Finset (Fin m → ℤ) :=
  (keysR n m r).offDiag.image shadowDifference

/-- Full characteristic-zero autocorrelation mass at a difference, whether or not it vanishes
after finite-field evaluation. -/
noncomputable def allShadowDifferenceMass (n m r : ℕ) (d : Fin m → ℤ) : ℕ :=
  ∑ p ∈ (keysR n m r).offDiag.filter (fun p => shadowDifference p = d),
    NR n m r p.1 * NR n m r p.2

/-- Centered coefficient attached to a difference vector. -/
def differenceDiscrepancyCoeff
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) (d : Fin m → ℤ) : ℝ :=
  (Fintype.card F : ℝ) * (if evalVec g m d = 0 then 1 else 0) - 1

theorem differenceDiscrepancyCoeff_of_eval_eq_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) {d : Fin m → ℤ} (hd : evalVec g m d = 0) :
    differenceDiscrepancyCoeff g m d = (Fintype.card F : ℝ) - 1 := by
  simp [differenceDiscrepancyCoeff, hd]

theorem differenceDiscrepancyCoeff_of_eval_ne_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) {d : Fin m → ℤ} (hd : evalVec g m d ≠ 0) :
    differenceDiscrepancyCoeff g m d = -1 := by
  simp [differenceDiscrepancyCoeff, hd]

/-- **Exact signed difference-fiber decomposition.** -/
theorem signedShadowPairDiscrepancy_eq_sum_differenceMass
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) :
    signedShadowPairDiscrepancy g n m r =
      ∑ d ∈ allShadowDifferences n m r,
        (allShadowDifferenceMass n m r d : ℝ) * differenceDiscrepancyCoeff g m d := by
  classical
  let P := (keysR n m r).offDiag
  let D := P.image shadowDifference
  let f : ((Fin m → ℤ) × (Fin m → ℤ)) → ℝ := fun p =>
    (NR n m r p.1 * NR n m r p.2 : ℝ) * differenceDiscrepancyCoeff g m (shadowDifference p)
  have hmaps : ∀ p ∈ P, shadowDifference p ∈ D :=
    fun p hp => Finset.mem_image_of_mem shadowDifference hp
  have hpair (p : (Fin m → ℤ) × (Fin m → ℤ)) :
      evalVec g m (shadowDifference p) = 0 ↔
        evalVec g m p.1 = evalVec g m p.2 := by
    rw [evalVec_shadowDifference, sub_eq_zero]
    exact eq_comm
  calc
    signedShadowPairDiscrepancy g n m r = ∑ p ∈ P, f p := by
      unfold signedShadowPairDiscrepancy f P differenceDiscrepancyCoeff
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_congr (hpair p)]
    _ = ∑ d ∈ D, ∑ p ∈ P.filter (fun p => shadowDifference p = d), f p :=
      (Finset.sum_fiberwise_of_maps_to (g := shadowDifference) (f := f) hmaps).symm
    _ = ∑ d ∈ D,
        (allShadowDifferenceMass n m r d : ℝ) * differenceDiscrepancyCoeff g m d := by
      apply Finset.sum_congr rfl
      intro d hd
      unfold f allShadowDifferenceMass
      rw [Nat.cast_sum]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hpd : shadowDifference p = d := (Finset.mem_filter.mp hp).2
      rw [hpd]
    _ = ∑ d ∈ allShadowDifferences n m r,
        (allShadowDifferenceMass n m r d : ℝ) * differenceDiscrepancyCoeff g m d := by
      rfl

end ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition.signedShadowPairDiscrepancy_eq_sum_differenceMass
