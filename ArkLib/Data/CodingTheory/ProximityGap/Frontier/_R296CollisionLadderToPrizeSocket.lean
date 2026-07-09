/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R294CollisionBudgetToPrizeSocket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R295MixedCollisionLadderSocket

/-!
# R296: collision ladder to the prize socket

R295 packages the repeated-index correction as a three-step collision ladder.
R294/R293 package the cubic-energy route consumed by the Jacobi-convolution
prize socket.  This file is the adapter between them.

The file proves no new cancellation estimate.  It records the exact hypotheses
under which the R295 ladder produces the R293 `CollisionBudgetRoute`, and then
feeds that route into the R294/R287 endpoint-upgrade consumer.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R296CollisionLadderToPrizeSocket

open ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket
open ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket
open ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket
open ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket

variable {m : ℕ} [NeZero m]

/-- View an R295 ladder profile as the R293 collision-reduced profile, once the
closed Wick bucket parameters `r,q` have been chosen. -/
def reducedProfileOfCollisionLadder
    (P : CollisionLadderProfile) (r q : ℝ) : CollisionReducedProfile where
  r := r
  q := q
  genericDistinctConnected := P.genericDistinctConnected
  collisionCorrection := P.collisionCorrection
  cubicEnergy := P.cubicEnergy

/-- The R295 closed Wick scalar is the R292 closed formula at the chosen
parameters. -/
def CollisionLadderUsesClosedWick
    (P : CollisionLadderProfile) (r q : ℝ) : Prop :=
  P.wickPerfectClosed = wickBucketClosed r q

/-- An R295 ladder decomposition becomes the R293 collision-reduced
decomposition after identifying the closed Wick bucket. -/
theorem collisionReducedDecomposition_of_collisionLadderDecomposition
    (P : CollisionLadderProfile) (r q : ℝ)
    (hwick : CollisionLadderUsesClosedWick P r q)
    (hdec : CollisionLadderDecomposition P) :
    CollisionReducedDecomposition (reducedProfileOfCollisionLadder P r q) := by
  unfold CollisionLadderUsesClosedWick at hwick
  unfold CollisionLadderDecomposition at hdec
  unfold CollisionReducedDecomposition reducedProfileOfCollisionLadder
  simp only
  rw [← hwick]
  exact hdec.2

/-- The R295 collision ladder supplies the R293 collision-budget route once the
generic-distinct-plus-Wick budget and the three ladder budgets are available. -/
theorem collisionBudgetRoute_of_collisionLadderBudgets
    (P : CollisionLadderProfile) (r q : ℝ)
    {Cgeneric Cmixed CtwoOne Ccube C scale : ℝ}
    (hwick : CollisionLadderUsesClosedWick P r q)
    (hdec : CollisionLadderDecomposition P)
    (hgeneric : P.wickPerfectClosed + P.genericDistinctConnected ≤ Cgeneric * scale)
    (hmixed : MixedCollisionBudget P.ladder Cmixed scale)
    (htwoOne : TwoOneTwoOneBudget P.ladder CtwoOne scale)
    (hcube : CubeCollisionBudget P.ladder Ccube scale)
    (hC : Cgeneric + Cmixed + CtwoOne + Ccube ≤ C) (hscale : 0 ≤ scale) :
    CollisionBudgetRoute (reducedProfileOfCollisionLadder P r q) C scale := by
  have hred :
      CollisionReducedDecomposition (reducedProfileOfCollisionLadder P r q) :=
    collisionReducedDecomposition_of_collisionLadderDecomposition P r q hwick hdec
  have hgen :
      GenericDistinctWithWickBudget (reducedProfileOfCollisionLadder P r q)
        Cgeneric scale := by
    unfold GenericDistinctWithWickBudget reducedProfileOfCollisionLadder
    unfold CollisionLadderUsesClosedWick at hwick
    simp only
    rw [← hwick]
    exact hgeneric
  have hcollR295 : ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket.CollisionBudget
      P (Cmixed + CtwoOne + Ccube) scale :=
    collisionBudget_of_ladderBudgets hdec hmixed htwoOne hcube le_rfl hscale
  have hcoll :
      ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket.CollisionBudget
        (reducedProfileOfCollisionLadder P r q) (Cmixed + CtwoOne + Ccube) scale := by
    unfold ArkLib.ProximityGap.Frontier.R295MixedCollisionLadderSocket.CollisionBudget at hcollR295
    unfold ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket.CollisionBudget
    unfold reducedProfileOfCollisionLadder
    simpa using hcollR295
  have hC' : Cgeneric + (Cmixed + CtwoOne + Ccube) ≤ C := by
    linarith
  exact collisionBudgetRoute hred hgen hcoll hC' hscale

/-- End-to-end consumer: R295 ladder budgets, plus the concrete profile
identifications and depth-three-to-ceiling upgrade, feed the R287 abstract
prize-floor socket. -/
theorem prizeFloor_of_collisionLadder_endpoint_upgrade_le_const
    (Ω : Type*) (P : CollisionLadderProfile) (r qR : ℝ)
    (J : ZMod m → ℂ) (q : ℕ)
    {B C Cgeneric Cmixed CtwoOne Ccube scale : ℝ}
    (hwick : CollisionLadderUsesClosedWick P r qR)
    (hdec : CollisionLadderDecomposition P)
    (hgeneric : P.wickPerfectClosed + P.genericDistinctConnected ≤ Cgeneric * scale)
    (hmixed : MixedCollisionBudget P.ladder Cmixed scale)
    (htwoOne : TwoOneTwoOneBudget P.ladder CtwoOne scale)
    (hcube : CubeCollisionBudget P.ladder Ccube scale)
    (hCB : Cgeneric + Cmixed + CtwoOne + Ccube ≤ B)
    (hscaleNonneg : 0 ≤ scale)
    (henergy :
      CollisionProfileIdentifiesTripleConv (reducedProfileOfCollisionLadder P r qR) J)
    (hscale : CollisionProfileUsesR23Scale (m := m) q scale)
    (hB0 : 0 ≤ B)
    (hBC : B ≤ C)
    (hBWick : B ≤ B ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C)
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω) :
    PrizeFloor Ω :=
  prizeFloor_of_collisionBudgetRoute_endpoint_upgrade_le_const Ω
    (reducedProfileOfCollisionLadder P r qR) J q henergy hscale hB0 hBC hBWick
    hupgrade hdeep hjacobi hfloor
    (collisionBudgetRoute_of_collisionLadderBudgets P r qR hwick hdec hgeneric
      hmixed htwoOne hcube hCB hscaleNonneg)

end ArkLib.ProximityGap.Frontier.R296CollisionLadderToPrizeSocket

open ArkLib.ProximityGap.Frontier.R296CollisionLadderToPrizeSocket in
#print axioms collisionReducedDecomposition_of_collisionLadderDecomposition
open ArkLib.ProximityGap.Frontier.R296CollisionLadderToPrizeSocket in
#print axioms collisionBudgetRoute_of_collisionLadderBudgets
open ArkLib.ProximityGap.Frontier.R296CollisionLadderToPrizeSocket in
#print axioms prizeFloor_of_collisionLadder_endpoint_upgrade_le_const
