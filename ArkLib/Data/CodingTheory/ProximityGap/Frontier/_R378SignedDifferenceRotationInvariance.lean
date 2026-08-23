/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R369SignedDifferenceMassDoubling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R372ShadowRelationRotationEquivariance

/-!
# R378: rotation preserves every signed endpoint summand

R371--R372 prove that negacyclic exponent rotation preserves the evaluation kernel and the shadow
histogram. R369 expresses the deep anomaly as a signed sum of doubled-walk endpoint masses. This
file welds the two: the complete signed summand is constant on every rotation orbit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition
open ArkLib.ProximityGap.Frontier.R369SignedDifferenceMassDoubling
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction
open ArkLib.ProximityGap.Frontier.R372ShadowRelationRotationEquivariance

/-- One signed doubled-walk endpoint contribution. -/
noncomputable def signedEndpointSummand
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (d : Fin m → ℤ) : ℝ :=
  (NR (2 * m) m (r + r) d : ℝ) * differenceDiscrepancyCoeff g m d

/-- Negacyclic rotation preserves endpoint `L1` mass exactly. -/
theorem endpointL1_rotZ (m : ℕ) (hm : 0 < m) (d : Fin m → ℤ) :
    endpointL1 (rotZ m hm d) = endpointL1 d := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold endpointL1
  rw [← Equiv.sum_comp (finRotate (m' + 1))
    (fun j => (rotZ (m' + 1) hm d j).natAbs)]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hlast : j = Fin.last m'
  · subst j
    rw [finRotate_last]
    unfold rotZ
    simp only [Fin.val_zero, if_true, Int.natAbs_neg]
    rfl
  · have hcoe : ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) = (j : ℕ) + 1 :=
      coe_finRotate_of_ne_last hlast
    unfold rotZ
    rw [if_neg (by rw [hcoe]; omega)]
    congr 2
    apply Fin.ext
    change ((finRotate (m' + 1) j : Fin (m' + 1)) : ℕ) - 1 = (j : ℕ)
    omega

/-- The centered coefficient is rotation-invariant because rotation multiplies evaluation by the
nonzero scalar `g`. -/
theorem differenceDiscrepancyCoeff_rotZ
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    differenceDiscrepancyCoeff g m (rotZ m hm d) = differenceDiscrepancyCoeff g m d := by
  unfold differenceDiscrepancyCoeff
  rw [if_congr (rotZ_eval_zero_iff m g hm hg hg0 d)] <;> rfl

/-- **Rotation invariance of the full signed endpoint mass.** -/
theorem signedEndpointSummand_rotZ
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    signedEndpointSummand g m r (rotZ m hm d) = signedEndpointSummand g m r d := by
  unfold signedEndpointSummand
  rw [NR_rotZ (2 * m) m (r + r) hm rfl,
    differenceDiscrepancyCoeff_rotZ g m hm hg hg0 d]

end ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance.endpointL1_rotZ
#print axioms
  ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance.differenceDiscrepancyCoeff_rotZ
#print axioms
  ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance.signedEndpointSummand_rotZ
