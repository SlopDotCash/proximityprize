/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R23TripleConvEnergyInput
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R287JacobiConvolutionSubconvexitySocket
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R293CollisionBudgetReductionSocket

/-!
# R294: collision-budget route to the R287 prize socket

R293 isolates the signed sextic route as a scalar collision-reduced profile.
This file records the exact final bookkeeping needed to consume such a scalar
profile as the concrete R23 `TripleConvEnergyBound`, and then as the R287
rung-three-to-ceiling prize route.

No analytic cancellation is proved here.  The open content is pushed into the
profile identifications and the R293 generic/collision budgets.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket

open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R293CollisionBudgetReductionSocket
open ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket

variable {m : ℕ} [NeZero m]

/-- The R293 scalar profile's cubic-energy coordinate is the actual R23
triple-convolution energy of the Jacobi coefficient sequence. -/
def CollisionProfileIdentifiesTripleConv
    (P : CollisionReducedProfile) (J : ZMod m → ℂ) : Prop :=
  P.cubicEnergy = ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2

/-- The scalar scale used by the R293 route is the R23 Wick scale `m^3 q^3`. -/
def CollisionProfileUsesR23Scale (q : ℕ) (scale : ℝ) : Prop :=
  scale = (m : ℝ) ^ 3 * (q : ℝ) ^ 3

/-- A collision-reduced scalar cubic bound becomes the concrete R23
`TripleConvEnergyBound` once its energy and scale are identified with the R23
objects. -/
theorem tripleConvEnergyBound_of_collisionReducedCubicScaleBound
    (P : CollisionReducedProfile) (J : ZMod m → ℂ) (q : ℕ) {C scale : ℝ}
    (henergy : CollisionProfileIdentifiesTripleConv P J)
    (hscale : CollisionProfileUsesR23Scale (m := m) q scale)
    (hbound : CubicScaleBound P C scale) :
    TripleConvEnergyBound J q C := by
  unfold CollisionProfileIdentifiesTripleConv at henergy
  unfold CollisionProfileUsesR23Scale at hscale
  unfold CubicScaleBound at hbound
  rw [hscale] at hbound
  unfold TripleConvEnergyBound
  rw [← henergy]
  simpa [mul_assoc] using hbound

/-- Packaged R293 route consumer for the R23 named rung-three input. -/
theorem tripleConvEnergyBound_of_collisionBudgetRoute
    (P : CollisionReducedProfile) (J : ZMod m → ℂ) (q : ℕ) {C scale : ℝ}
    (henergy : CollisionProfileIdentifiesTripleConv P J)
    (hscale : CollisionProfileUsesR23Scale (m := m) q scale)
    (hroute : CollisionBudgetRoute P C scale) :
    TripleConvEnergyBound J q C :=
  tripleConvEnergyBound_of_collisionReducedCubicScaleBound P J q henergy hscale
    hroute.cubicBound

/-- Packaged R293 route consumer for R287's concrete rung-three predicate. -/
theorem concreteRungThreeSubconvex_of_collisionBudgetRoute
    (P : CollisionReducedProfile) (J : ZMod m → ℂ) (q : ℕ) {C scale : ℝ}
    (henergy : CollisionProfileIdentifiesTripleConv P J)
    (hscale : CollisionProfileUsesR23Scale (m := m) q scale)
    (hroute : CollisionBudgetRoute P C scale) :
    ConcreteRungThreeSubconvex J q C :=
  tripleConvEnergyBound_of_collisionBudgetRoute P J q henergy hscale hroute

/-- End-to-end consumer: a collision-reduced R293 route, plus a named
depth-three-to-ceiling upgrade, feeds the R287 abstract prize-floor socket.
The relaxed constant form lets the signed sextic/collision route publish a
sharp R23 constant `B`, while the deep upgrade uses any larger campaign Wick
constant `C`. -/
theorem prizeFloor_of_collisionBudgetRoute_endpoint_upgrade_le_const
    (Ω : Type*) (P : CollisionReducedProfile) (J : ZMod m → ℂ) (q : ℕ)
    {B C scale : ℝ}
    (henergy : CollisionProfileIdentifiesTripleConv P J)
    (hscale : CollisionProfileUsesR23Scale (m := m) q scale)
    (hB0 : 0 ≤ B)
    (hBC : B ≤ C)
    (hBWick : B ≤ B ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C)
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (hroute : CollisionBudgetRoute P B scale) :
    PrizeFloor Ω :=
  prizeFloor_of_concreteRungThree_endpoint_upgrade_le_const Ω J q
    hB0 hBC hBWick hupgrade hdeep hjacobi hfloor
    (concreteRungThreeSubconvex_of_collisionBudgetRoute P J q henergy hscale hroute)

end ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket

open ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket in
#print axioms tripleConvEnergyBound_of_collisionReducedCubicScaleBound
open ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket in
#print axioms tripleConvEnergyBound_of_collisionBudgetRoute
open ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket in
#print axioms concreteRungThreeSubconvex_of_collisionBudgetRoute
open ArkLib.ProximityGap.Frontier.R294CollisionBudgetToPrizeSocket in
#print axioms prizeFloor_of_collisionBudgetRoute_endpoint_upgrade_le_const
