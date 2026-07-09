/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R368SignedDifferenceFiberDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R371ShadowKernelRotationAction

/-!
# R378: rotation preserves the signed kernel coefficient

R371 proves that negacyclic exponent rotation preserves the evaluation kernel.  This file welds
that action to R368's signed coefficient: kernel differences remain weighted by `q-1`, and
non-kernel differences remain weighted by `-1`, throughout every rotation orbit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R368SignedDifferenceFiberDecomposition
open ArkLib.ProximityGap.Frontier.R371ShadowKernelRotationAction

/-- The centered coefficient is rotation-invariant because rotation multiplies evaluation by the
nonzero scalar `g`. -/
theorem differenceDiscrepancyCoeff_rotZ
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    differenceDiscrepancyCoeff g m (rotZ m hm d) = differenceDiscrepancyCoeff g m d := by
  unfold differenceDiscrepancyCoeff
  rw [if_congr (rotZ_eval_zero_iff m g hm hg hg0 d)] <;> rfl

end ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance.differenceDiscrepancyCoeff_rotZ
