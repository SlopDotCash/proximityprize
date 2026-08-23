/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R381SignedRotationOrbitBlock

/-!
# R382: rotation-orbit compression supplies no internal cancellation

R381 groups the exact signed endpoint discrepancy into negacyclic rotation orbits.  This file
performs the adversarial audit of that grouping: every summand on one orbit is equal, hence the
absolute value of the orbit sum is exactly the sum of the absolute values.  The orbit-size gain
from R380 is therefore canceled exactly by the orbit multiplicity in the discrepancy.

Any successful continuation must compare distinct rotation orbits or use arithmetic information
not contained in orbit size, support, endpoint mass, kernel sign, or doubled-walk multiplicity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R382RotationOrbitNoCancellation

open ArkLib.ProximityGap.Frontier.R378SignedDifferenceRotationInvariance
open ArkLib.ProximityGap.Frontier.R380ConcreteSparseRotationOrbit
open ArkLib.ProximityGap.Frontier.R381SignedRotationOrbitBlock

/-- The absolute orbit-block contribution is its cardinality times the representative's
absolute contribution. -/
theorem abs_sum_rotationOrbit_signedEndpointSummand
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    |∑ e ∈ rotationOrbit m hm d, signedEndpointSummand g m r e| =
      (rotationOrbit m hm d).card * |signedEndpointSummand g m r d| := by
  rw [sum_rotationOrbit_signedEndpointSummand g m r hm hg hg0 d]
  simp [abs_mul]

/-- **No-cancellation identity.** Triangle inequality on a rotation block is an equality. -/
theorem abs_sum_rotationOrbit_eq_sum_abs
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) (hg : g ^ m = -1) (hg0 : g ≠ 0)
    (d : Fin m → ℤ) :
    |∑ e ∈ rotationOrbit m hm d, signedEndpointSummand g m r e| =
      ∑ e ∈ rotationOrbit m hm d, |signedEndpointSummand g m r e| := by
  rw [abs_sum_rotationOrbit_signedEndpointSummand g m r hm hg hg0 d]
  calc
    ((rotationOrbit m hm d).card : ℝ) * |signedEndpointSummand g m r d| =
        ∑ _e ∈ rotationOrbit m hm d, |signedEndpointSummand g m r d| := by simp
    _ = ∑ e ∈ rotationOrbit m hm d, |signedEndpointSummand g m r e| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [signedEndpointSummand_eq_of_mem_rotationOrbit g m r hm hg hg0 d he]

end ArkLib.ProximityGap.Frontier.R382RotationOrbitNoCancellation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R382RotationOrbitNoCancellation.abs_sum_rotationOrbit_eq_sum_abs
