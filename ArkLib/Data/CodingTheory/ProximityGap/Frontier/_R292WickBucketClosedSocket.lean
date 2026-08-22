/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# R292: closed Wick bucket socket

For the R291 constrained sextic split, the Wick-perfect-matching bucket has a closed scalar
formula when the nonzero Jacobi coefficients consist of one small coefficient with norm-square
`1` and `r = m-2` large coefficients with norm-square `q`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R292WickBucketClosedSocket

/-- Closed Wick-perfect bucket for one small nonzero coefficient and `r` large coefficients. -/
def wickBucketClosed (r q : ℝ) : ℝ :=
  1 + r * (6 * r ^ 2 - 9 * r + 4) * q ^ 3
    + 9 * r * (2 * r - 1) * q ^ 2
    + 9 * r * q

/-- The equivalent unordered-multiset shape expansion. -/
noncomputable def wickBucketByShape (r q : ℝ) : ℝ :=
  (1 + r * q ^ 3)
    + 9 * (r * q + r * q ^ 2 + r * (r - 1) * q ^ 3)
    + 36 * ((r * (r - 1) / 2) * q ^ 2
      + (r * (r - 1) * (r - 2) / 6) * q ^ 3)

/-- The compact polynomial and shape expansions agree. -/
theorem wickBucketClosed_eq_byShape (r q : ℝ) :
    wickBucketClosed r q = wickBucketByShape r q := by
  unfold wickBucketClosed wickBucketByShape
  ring

/-- Profile after removing the closed Wick bucket from the unknown part. -/
structure ClosedWickProfile where
  r : ℝ
  q : ℝ
  genericDistinctConnected : ℝ
  collisionCorrection : ℝ
  cubicEnergy : ℝ

/-- Exact decomposition using the closed Wick bucket. -/
def ClosedWickDecomposition (P : ClosedWickProfile) : Prop :=
  P.cubicEnergy =
    wickBucketClosed P.r P.q + P.genericDistinctConnected + P.collisionCorrection

/-- The remaining analytic budget after the closed Wick bucket is removed. -/
def RemainingConnectedBudget (P : ClosedWickProfile) (C scale : ℝ) : Prop :=
  P.genericDistinctConnected + P.collisionCorrection
    ≤ C * scale - wickBucketClosed P.r P.q

/-- Final cubic-scale bound. -/
def CubicScaleBound (P : ClosedWickProfile) (C scale : ℝ) : Prop :=
  P.cubicEnergy ≤ C * scale

/-- Consuming the remaining connected budget after substituting the closed Wick bucket. -/
theorem cubicScaleBound_of_remainingConnectedBudget
    {P : ClosedWickProfile} {C scale : ℝ}
    (hdec : ClosedWickDecomposition P)
    (hrem : RemainingConnectedBudget P C scale) :
    CubicScaleBound P C scale := by
  unfold ClosedWickDecomposition at hdec
  unfold RemainingConnectedBudget CubicScaleBound at *
  rw [hdec]
  linarith

end ArkLib.ProximityGap.Frontier.R292WickBucketClosedSocket

open ArkLib.ProximityGap.Frontier.R292WickBucketClosedSocket in
#print axioms wickBucketClosed_eq_byShape
open ArkLib.ProximityGap.Frontier.R292WickBucketClosedSocket in
#print axioms cubicScaleBound_of_remainingConnectedBudget
