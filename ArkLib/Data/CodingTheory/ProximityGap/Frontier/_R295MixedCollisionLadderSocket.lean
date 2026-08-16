/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# R295: mixed-collision ladder socket

R294 splits the collision correction into eight repeated-index strata.  R295 groups those
strata by expected difficulty: mixed distinct/two-one first, two-one/two-one second, and
cube-involving cleanup last.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket

/-- Three-term collision ladder extracted from the eight R294 collision strata. -/
structure CollisionLadder where
  mixedDistinctTwoOne : ℝ
  twoOneTwoOne : ℝ
  cubeInvolving : ℝ

/-- Total repeated-index correction in the R295 ladder grouping. -/
def CollisionLadder.total (L : CollisionLadder) : ℝ :=
  L.mixedDistinctTwoOne + L.twoOneTwoOne + L.cubeInvolving

/-- Exact ladder decomposition of the R293 collision correction. -/
structure CollisionLadderProfile where
  ladder : CollisionLadder
  collisionCorrection : ℝ
  cubicEnergy : ℝ
  wickPerfectClosed : ℝ
  genericDistinctConnected : ℝ

/-- The collision correction is the ladder total, and the cubic energy is Wick + generic +
collision. -/
def CollisionLadderDecomposition (P : CollisionLadderProfile) : Prop :=
  P.collisionCorrection = P.ladder.total ∧
    P.cubicEnergy = P.wickPerfectClosed + P.genericDistinctConnected + P.collisionCorrection

/-- Budget for the mixed `(111,21) + (21,111)` five-point collision family. -/
def MixedCollisionBudget (L : CollisionLadder) (C scale : ℝ) : Prop :=
  L.mixedDistinctTwoOne ≤ C * scale

/-- Budget for the repeated/repeated four-point collision family. -/
def TwoOneTwoOneBudget (L : CollisionLadder) (C scale : ℝ) : Prop :=
  L.twoOneTwoOne ≤ C * scale

/-- Budget for all cube-involving collision strata. -/
def CubeCollisionBudget (L : CollisionLadder) (C scale : ℝ) : Prop :=
  L.cubeInvolving ≤ C * scale

/-- Aggregate collision budget after the ladder estimates. -/
def CollisionBudget (P : CollisionLadderProfile) (C scale : ℝ) : Prop :=
  P.collisionCorrection ≤ C * scale

/-- The three ladder budgets imply the aggregate collision budget. -/
theorem collisionBudget_of_ladderBudgets
    {P : CollisionLadderProfile} {Cmixed CtwoOne Ccube C scale : ℝ}
    (hdec : CollisionLadderDecomposition P)
    (hmixed : MixedCollisionBudget P.ladder Cmixed scale)
    (htwoOne : TwoOneTwoOneBudget P.ladder CtwoOne scale)
    (hcube : CubeCollisionBudget P.ladder Ccube scale)
    (hC : Cmixed + CtwoOne + Ccube ≤ C) (hscale : 0 ≤ scale) :
    CollisionBudget P C scale := by
  unfold CollisionLadderDecomposition at hdec
  unfold MixedCollisionBudget TwoOneTwoOneBudget CubeCollisionBudget CollisionBudget at *
  rw [hdec.1]
  unfold CollisionLadder.total
  calc
    P.ladder.mixedDistinctTwoOne + P.ladder.twoOneTwoOne + P.ladder.cubeInvolving
        ≤ Cmixed * scale + CtwoOne * scale + Ccube * scale := by linarith
    _ = (Cmixed + CtwoOne + Ccube) * scale := by ring
    _ ≤ C * scale := mul_le_mul_of_nonneg_right hC hscale

/-- R295 final consumer: generic-distinct control plus the collision ladder gives the cubic
energy bound. -/
theorem cubicEnergy_bound_of_generic_and_collisionLadder
    {P : CollisionLadderProfile} {Cgeneric Cmixed CtwoOne Ccube C scale : ℝ}
    (hdec : CollisionLadderDecomposition P)
    (hgeneric : P.wickPerfectClosed + P.genericDistinctConnected ≤ Cgeneric * scale)
    (hmixed : MixedCollisionBudget P.ladder Cmixed scale)
    (htwoOne : TwoOneTwoOneBudget P.ladder CtwoOne scale)
    (hcube : CubeCollisionBudget P.ladder Ccube scale)
    (hC : Cgeneric + Cmixed + CtwoOne + Ccube ≤ C) (hscale : 0 ≤ scale) :
    P.cubicEnergy ≤ C * scale := by
  have hcoll : CollisionBudget P (Cmixed + CtwoOne + Ccube) scale :=
    collisionBudget_of_ladderBudgets hdec hmixed htwoOne hcube (le_rfl) hscale
  unfold CollisionLadderDecomposition at hdec
  unfold CollisionBudget at hcoll
  rw [hdec.2]
  calc
    P.wickPerfectClosed + P.genericDistinctConnected + P.collisionCorrection
        ≤ Cgeneric * scale + (Cmixed + CtwoOne + Ccube) * scale := by linarith
    _ = (Cgeneric + Cmixed + CtwoOne + Ccube) * scale := by ring
    _ ≤ C * scale := mul_le_mul_of_nonneg_right hC hscale

end ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket

open ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket in
#print axioms collisionBudget_of_ladderBudgets
open ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket in
#print axioms cubicEnergy_bound_of_generic_and_collisionLadder
