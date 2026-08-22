/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# R294: collision-strata map socket

The old R41 split isolates only the cube-cube sextic shape.  R293's collision correction is
the sum of all connected repeated-index strata on the R289 hyperplane, excluding the closed
Wick-perfect bucket and excluding the fully distinct connected six-point bucket.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R294CollisionStrataMapSocket

/-- Three possible equality profiles for one side of a triple. -/
inductive TripleShape where
  | allEqual
  | twoOne
  | allDistinct
  deriving DecidableEq, Repr

/-- A pair of left/right triple profiles in the constrained sextic expansion. -/
structure SexticShape where
  left : TripleShape
  right : TripleShape
  deriving DecidableEq, Repr

/-- The fully distinct connected bucket is not part of the collision correction. -/
def genericDistinctShape : SexticShape :=
  ⟨TripleShape.allDistinct, TripleShape.allDistinct⟩

/-- The old R41 cube shape: both triples internally all equal. -/
def cubeCubeShape : SexticShape :=
  ⟨TripleShape.allEqual, TripleShape.allEqual⟩

/-- A collision shape is any repeated-index shape except the fully distinct bucket. -/
def IsCollisionShape (s : SexticShape) : Prop :=
  s ≠ genericDistinctShape

/-- The eight R293 collision strata, grouped by left/right equality profile. -/
structure CollisionStrata where
  cubeCube : ℝ
  cubeTwoOne : ℝ
  twoOneCube : ℝ
  twoOneTwoOne : ℝ
  cubeDistinct : ℝ
  distinctCube : ℝ
  twoOneDistinct : ℝ
  distinctTwoOne : ℝ

/-- Sum of all repeated-index connected collision strata. -/
def CollisionStrata.total (S : CollisionStrata) : ℝ :=
  S.cubeCube + S.cubeTwoOne + S.twoOneCube + S.twoOneTwoOne
    + S.cubeDistinct + S.distinctCube + S.twoOneDistinct + S.distinctTwoOne

/-- R293 profile with the collision correction exposed as a sum of repeated-index strata. -/
structure CollisionStrataProfile where
  genericDistinctConnected : ℝ
  wickPerfectClosed : ℝ
  strata : CollisionStrata
  collisionCorrection : ℝ
  cubicEnergy : ℝ

/-- Exact collision-strata decomposition. -/
def CollisionStrataDecomposition (P : CollisionStrataProfile) : Prop :=
  P.collisionCorrection = P.strata.total ∧
    P.cubicEnergy = P.wickPerfectClosed + P.genericDistinctConnected + P.collisionCorrection

/-- A direct per-stratum budget interface for the repeated-index correction. -/
def CollisionStrataBudget (S : CollisionStrata) (C scale : ℝ) : Prop :=
  S.total ≤ C * scale

/-- R293's aggregate collision budget. -/
def CollisionBudget (P : CollisionStrataProfile) (C scale : ℝ) : Prop :=
  P.collisionCorrection ≤ C * scale

/-- The old cube split controls exactly the cube-cube shape among the R293 collision strata. -/
theorem oldCubeSplit_covers_cubeCube_only :
    cubeCubeShape.left = TripleShape.allEqual ∧ cubeCubeShape.right = TripleShape.allEqual ∧
      IsCollisionShape cubeCubeShape := by
  constructor
  · rfl
  constructor
  · rfl
  · intro h
    cases h

/-- Per-stratum control implies the aggregate R293 collision budget. -/
theorem collisionBudget_of_collisionStrataBudget
    {P : CollisionStrataProfile} {C scale : ℝ}
    (hdec : CollisionStrataDecomposition P)
    (hstrata : CollisionStrataBudget P.strata C scale) :
    CollisionBudget P C scale := by
  unfold CollisionStrataDecomposition at hdec
  unfold CollisionStrataBudget CollisionBudget at *
  rw [hdec.1]
  exact hstrata

/-- Generic-distinct plus collision-strata budgets imply a final cubic energy bound. -/
theorem cubicEnergy_bound_of_strata_and_generic
    {P : CollisionStrataProfile} {Cgeneric Ccollision C scale : ℝ}
    (hdec : CollisionStrataDecomposition P)
    (hgeneric : P.wickPerfectClosed + P.genericDistinctConnected ≤ Cgeneric * scale)
    (hstrata : CollisionStrataBudget P.strata Ccollision scale)
    (hC : Cgeneric + Ccollision ≤ C) (hscale : 0 ≤ scale) :
    P.cubicEnergy ≤ C * scale := by
  have hcoll : CollisionBudget P Ccollision scale :=
    collisionBudget_of_collisionStrataBudget hdec hstrata
  unfold CollisionStrataDecomposition at hdec
  unfold CollisionBudget at hcoll
  rw [hdec.2]
  calc
    P.wickPerfectClosed + P.genericDistinctConnected + P.collisionCorrection
        ≤ Cgeneric * scale + Ccollision * scale := by linarith
    _ = (Cgeneric + Ccollision) * scale := by ring
    _ ≤ C * scale := mul_le_mul_of_nonneg_right hC hscale

end ArkLib.ProximityGap.Frontier.R294CollisionStrataMapSocket

open ArkLib.ProximityGap.Frontier.R294CollisionStrataMapSocket in
#print axioms oldCubeSplit_covers_cubeCube_only
open ArkLib.ProximityGap.Frontier.R294CollisionStrataMapSocket in
#print axioms collisionBudget_of_collisionStrataBudget
open ArkLib.ProximityGap.Frontier.R294CollisionStrataMapSocket in
#print axioms cubicEnergy_bound_of_strata_and_generic
