/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# R293: collision-budget reduction socket

R293 isolates the repeated-index collision strata as a separate lower-dimensional budget.
The remaining large signed term is the generic fully distinct connected six-point bucket.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket

/-- Closed Wick-perfect bucket from R292, repeated here to keep this socket independent in
`lake env lean` iteration. -/
def wickBucketClosed (r q : ℝ) : ℝ :=
  1 + r * (6 * r ^ 2 - 9 * r + 4) * q ^ 3
    + 9 * r * (2 * r - 1) * q ^ 2
    + 9 * r * q

/-- R293 profile: closed Wick bucket plus generic distinct connected bucket plus collision
correction. -/
structure CollisionReducedProfile where
  r : ℝ
  q : ℝ
  genericDistinctConnected : ℝ
  collisionCorrection : ℝ
  cubicEnergy : ℝ

/-- Exact decomposition using the R292 closed Wick bucket. -/
def CollisionReducedDecomposition (P : CollisionReducedProfile) : Prop :=
  P.cubicEnergy =
    wickBucketClosed P.r P.q + P.genericDistinctConnected + P.collisionCorrection

/-- Main signed generic-distinct budget after the closed Wick bucket is included. -/
def GenericDistinctWithWickBudget (P : CollisionReducedProfile) (C scale : ℝ) : Prop :=
  wickBucketClosed P.r P.q + P.genericDistinctConnected ≤ C * scale

/-- Separate repeated-index collision budget. -/
def CollisionBudget (P : CollisionReducedProfile) (C scale : ℝ) : Prop :=
  P.collisionCorrection ≤ C * scale

/-- Final cubic-scale bound. -/
def CubicScaleBound (P : CollisionReducedProfile) (C scale : ℝ) : Prop :=
  P.cubicEnergy ≤ C * scale

/-- Generic-distinct plus collision budgets imply the cubic energy bound. -/
theorem cubicScaleBound_of_genericDistinct_and_collisionBudget
    {P : CollisionReducedProfile} {Cgeneric Ccollision C scale : ℝ}
    (hdec : CollisionReducedDecomposition P)
    (hgen : GenericDistinctWithWickBudget P Cgeneric scale)
    (hcoll : CollisionBudget P Ccollision scale)
    (hC : Cgeneric + Ccollision ≤ C) (hscale : 0 ≤ scale) :
    CubicScaleBound P C scale := by
  unfold CollisionReducedDecomposition at hdec
  unfold GenericDistinctWithWickBudget CollisionBudget CubicScaleBound at *
  rw [hdec]
  calc
    wickBucketClosed P.r P.q + P.genericDistinctConnected + P.collisionCorrection
        ≤ Cgeneric * scale + Ccollision * scale := by linarith
    _ = (Cgeneric + Ccollision) * scale := by ring
    _ ≤ C * scale := mul_le_mul_of_nonneg_right hC hscale

/-- Packaged collision-budget route. -/
structure CollisionBudgetRoute (P : CollisionReducedProfile) (C scale : ℝ) where
  decomposition : CollisionReducedDecomposition P
  cubicBound : CubicScaleBound P C scale

/-- Build the packaged route from the generic and collision estimates. -/
def collisionBudgetRoute
    {P : CollisionReducedProfile} {Cgeneric Ccollision C scale : ℝ}
    (hdec : CollisionReducedDecomposition P)
    (hgen : GenericDistinctWithWickBudget P Cgeneric scale)
    (hcoll : CollisionBudget P Ccollision scale)
    (hC : Cgeneric + Ccollision ≤ C) (hscale : 0 ≤ scale) :
    CollisionBudgetRoute P C scale :=
  ⟨hdec, cubicScaleBound_of_genericDistinct_and_collisionBudget hdec hgen hcoll hC hscale⟩

end ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket

open ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket in
#print axioms cubicScaleBound_of_genericDistinct_and_collisionBudget
open ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket in
#print axioms collisionBudgetRoute
