/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# R291: generic distinct-six socket

R291 refines the signed connected sextic route: the observed connected mass is concentrated
in the fully distinct left/right six-point bucket.  Repeated-index collision strata are then
treated as correction terms.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R291GenericDistinctSixSocket

/-- Scalar decomposition of the constrained sextic cubic energy into Wick, generic
distinct-connected, and collision-correction pieces. -/
structure GenericDistinctSixProfile where
  wickPerfectMatching : ℝ
  genericDistinctConnected : ℝ
  collisionCorrection : ℝ
  cubicEnergy : ℝ

/-- Exact signed decomposition after splitting the connected term by collision stratum. -/
def GenericDistinctSixDecomposition (P : GenericDistinctSixProfile) : Prop :=
  P.cubicEnergy =
    P.wickPerfectMatching + P.genericDistinctConnected + P.collisionCorrection

/-- The main generic distinct-six subconvexity statement. -/
def GenericDistinctSixMainBound (P : GenericDistinctSixProfile) (C scale : ℝ) : Prop :=
  P.wickPerfectMatching + P.genericDistinctConnected ≤ C * scale

/-- Collision strata are lower-order or otherwise separately budgeted. -/
def CollisionCorrectionBound (P : GenericDistinctSixProfile) (C scale : ℝ) : Prop :=
  P.collisionCorrection ≤ C * scale

/-- Final cubic-scale bound for the profile. -/
def CubicScaleBound (P : GenericDistinctSixProfile) (C scale : ℝ) : Prop :=
  P.cubicEnergy ≤ C * scale

/-- Consuming the generic-distinct main bound and the collision correction budget. -/
theorem cubicScaleBound_of_genericDistinctSix
    {P : GenericDistinctSixProfile} {Cmain Ccollision C scale : ℝ}
    (hdec : GenericDistinctSixDecomposition P)
    (hmain : GenericDistinctSixMainBound P Cmain scale)
    (hcoll : CollisionCorrectionBound P Ccollision scale)
    (hC : Cmain + Ccollision ≤ C) (hscale : 0 ≤ scale) :
    CubicScaleBound P C scale := by
  unfold GenericDistinctSixDecomposition at hdec
  unfold GenericDistinctSixMainBound CollisionCorrectionBound CubicScaleBound at *
  rw [hdec]
  calc
    P.wickPerfectMatching + P.genericDistinctConnected + P.collisionCorrection
        ≤ Cmain * scale + Ccollision * scale := by linarith
    _ = (Cmain + Ccollision) * scale := by ring
    _ ≤ C * scale := mul_le_mul_of_nonneg_right hC hscale

/-- Packaged R291 route. -/
structure GenericDistinctSixRoute (P : GenericDistinctSixProfile) (C scale : ℝ) where
  decomposition : GenericDistinctSixDecomposition P
  cubicBound : CubicScaleBound P C scale

/-- Build the packaged route from the two split estimates. -/
def genericDistinctSixRoute
    {P : GenericDistinctSixProfile} {Cmain Ccollision C scale : ℝ}
    (hdec : GenericDistinctSixDecomposition P)
    (hmain : GenericDistinctSixMainBound P Cmain scale)
    (hcoll : CollisionCorrectionBound P Ccollision scale)
    (hC : Cmain + Ccollision ≤ C) (hscale : 0 ≤ scale) :
    GenericDistinctSixRoute P C scale :=
  ⟨hdec, cubicScaleBound_of_genericDistinctSix hdec hmain hcoll hC hscale⟩

end ArkLib.ProximityGap.Frontier.R291GenericDistinctSixSocket

open ArkLib.ProximityGap.Frontier.R291GenericDistinctSixSocket in
#print axioms cubicScaleBound_of_genericDistinctSix
open ArkLib.ProximityGap.Frontier.R291GenericDistinctSixSocket in
#print axioms genericDistinctSixRoute
