/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R287 Jacobi-convolution subconvexity socket)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R66TripleConvIterWickAdapter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R88TripleConvConstantAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R90IterConvWickConstantAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R96IterConvBudgetMonotoneAdapters

/-!
# R287 (#466): Jacobi-convolution subconvexity socket

R27's `fullTower_collapse` identifies the corrected hyperplane-cancellation
problem with growth of iterated convolutions of the Jacobi coefficient sequence.
This lightweight socket records the proof-shape without importing the heavy
frontier tower:

* `RungThreeSubconvex` is the first non-Weil subconvexity rung.
* `DeepJacobiSubconvex` is the `r ≈ log q` ladder statement.
* `HyperplaneSubconvex` is the prize-facing incidence cancellation.

The real analytic task is to prove the first two predicates for the concrete
Jacobi sequence; this file only records the consumer wiring.
-/

namespace ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket

open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters
open ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters

variable {m : ℕ} [NeZero m]

/-- Abstract label for the rung-3 Jacobi-convolution subconvexity input. -/
def RungThreeSubconvex (Ω : Type*) : Prop := Nonempty Ω

/-- Abstract label for the deep `IterConvEnergyWick` ladder up to `r ≈ log q`. -/
def DeepJacobiSubconvex (Ω : Type*) : Prop := Nonempty Ω

/-- Abstract label for the corrected off-diagonal hyperplane incidence cancellation. -/
def HyperplaneSubconvex (Ω : Type*) : Prop := Nonempty Ω

/-- Abstract label for the prize-floor conclusion supplied by the existing
incidence consumer. -/
def PrizeFloor (Ω : Type*) : Prop := Nonempty Ω

/-- The Jacobi-convolution subconvexity package: the first open rung plus the
deep ladder statement. -/
def JacobiSubconvexityPackage (Ω : Type*) : Prop :=
  RungThreeSubconvex Ω ∧ DeepJacobiSubconvex Ω

/-- If rung 3 can be promoted to the deep ladder, then the Jacobi package holds.
This isolates the mathematical upgrade R287 is looking for. -/
theorem jacobiPackage_of_rungThree_upgrade
    (Ω : Type*) (hupgrade : RungThreeSubconvex Ω → DeepJacobiSubconvex Ω)
    (h3 : RungThreeSubconvex Ω) :
    JacobiSubconvexityPackage Ω :=
  ⟨h3, hupgrade h3⟩

/-- The Jacobi package feeds the hyperplane subconvexity input once the concrete
R27 tower consumer is supplied. -/
theorem hyperplaneSubconvex_of_jacobiPackage
    (Ω : Type*) (hconsume : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hpack : JacobiSubconvexityPackage Ω) :
    HyperplaneSubconvex Ω :=
  hconsume hpack.2

/-- End-to-end abstract consumer for the R287 route: a rung-3-to-deep upgrade,
the concrete Jacobi-to-hyperplane consumer, and the existing incidence-to-floor
consumer together pin the prize floor.  The only mathematical inputs still
exposed are exactly the rung-3 subconvexity input and the two concrete
consumers. -/
theorem prizeFloor_of_rungThree_upgrade
    (Ω : Type*) (hupgrade : RungThreeSubconvex Ω → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (h3 : RungThreeSubconvex Ω) :
    PrizeFloor Ω :=
  hfloor (hjacobi (hupgrade h3))

/-! ## Concrete `TripleConvEnergyBound` / `IterConvEnergyWick` face -/

/-- Concrete R287 rung-3 input, using the calibrated R23 name. -/
def ConcreteRungThreeSubconvex (J : ZMod m → ℂ) (q : ℕ) (B : ℝ) : Prop :=
  TripleConvEnergyBound J q B

/-- Concrete finite-depth Jacobi-convolution ladder, using the R27 full-tower
`IterConvEnergyWick` name. -/
def ConcreteDeepJacobiSubconvexUpTo (J : ZMod m → ℂ) (q R : ℕ) (C : ℝ) : Prop :=
  ∀ r : ℕ, 3 ≤ r → r ≤ R → IterConvEnergyWick J q r C

/-- Concrete log-depth Jacobi-convolution endpoint. -/
def ConcreteDeepJacobiCeilSubconvex (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  IterConvEnergyWick J q ⌈Real.log (q : ℝ)⌉₊ C

/-- The concrete depth-3-to-log-depth upgrade demanded by the R287 route.
This is the prize-relevant analytic step: promote the calibrated depth-3 Wick
rung to the ceiling-depth Jacobi-convolution endpoint at the same public
constant. -/
def ConcreteDepthThreeToCeilUpgrade (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  IterConvEnergyWick J q 3 C → ConcreteDeepJacobiCeilSubconvex J q C

/-- Monotonicity of the concrete rung-3 input in its scalar budget. -/
theorem ConcreteRungThreeSubconvex.mono_const
    (J : ZMod m → ℂ) (q : ℕ) {B B' : ℝ}
    (hBB : B ≤ B') (h : ConcreteRungThreeSubconvex J q B) :
    ConcreteRungThreeSubconvex J q B' :=
  tripleConvEnergyBound_mono_const J q hBB h

/-- Restrict a concrete finite-depth ladder to a smaller endpoint. -/
theorem ConcreteDeepJacobiSubconvexUpTo.mono_depth
    (J : ZMod m → ℂ) (q : ℕ) {R R' : ℕ} {C : ℝ}
    (hRR : R' ≤ R) (h : ConcreteDeepJacobiSubconvexUpTo J q R C) :
    ConcreteDeepJacobiSubconvexUpTo J q R' C :=
  fun r h3 hr => h r h3 (hr.trans hRR)

/-- Monotonicity of the concrete finite-depth ladder in the Wick constant. -/
theorem ConcreteDeepJacobiSubconvexUpTo.mono_const
    (J : ZMod m → ℂ) (q R : ℕ) {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (h : ConcreteDeepJacobiSubconvexUpTo J q R C) :
    ConcreteDeepJacobiSubconvexUpTo J q R C' :=
  fun r h3 hr => iterConvEnergyWick_mono_const J q r hC0 hCC (h r h3 hr)

/-- Monotonicity of the concrete log-depth endpoint in the Wick constant. -/
theorem ConcreteDeepJacobiCeilSubconvex.mono_const
    (J : ZMod m → ℂ) (q : ℕ) {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (h : ConcreteDeepJacobiCeilSubconvex J q C) :
    ConcreteDeepJacobiCeilSubconvex J q C' :=
  iterConvEnergyWick_mono_const J q ⌈Real.log (q : ℝ)⌉₊ hC0 hCC h

/-- A calibrated triple-convolution certificate gives the concrete depth-3
Jacobi Wick rung. -/
theorem iterConvEnergyWick_three_of_concreteRungThree
    (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h3 : ConcreteRungThreeSubconvex J q B) :
    IterConvEnergyWick J q 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h3

/-- Concrete finite-depth package: if the depth-3 Wick rung upgrades to all
rungs through `R`, then a calibrated R23 certificate supplies the whole
finite-depth R287 ladder. -/
theorem concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_upgrade
    (J : ZMod m → ℂ) (q R : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade :
      IterConvEnergyWick J q 3 C → ConcreteDeepJacobiSubconvexUpTo J q R C)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiSubconvexUpTo J q R C :=
  hupgrade (iterConvEnergyWick_three_of_concreteRungThree J q hBC h3)

/-- Recurrence-only sufficient condition for the concrete finite-depth ladder:
the R95/R96 Cauchy propagation carries a calibrated rung-3 certificate to every
depth `r ≥ 3` provided the head budget `m ≤ 4*C` is available.  This is useful
bookkeeping, but the budget is linear in `m`, so it is not the desired
absolute-constant subconvexity upgrade. -/
theorem concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_left_budget
    (J : ZMod m → ℂ) (q R : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiSubconvexUpTo J q R C' :=
  fun r hr3 _hrR =>
    iterConvEnergyWick_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const
      J q r hJ hC0 hCC hBC hleft h3 hr3

/-- An up-to-ceiling concrete ladder gives the log-depth endpoint. -/
theorem concreteDeepJacobiCeilSubconvex_of_upTo
    (J : ZMod m → ℂ) (q : ℕ) (C : ℝ)
    (hceil : 3 ≤ ⌈Real.log (q : ℝ)⌉₊)
    (hup :
      ConcreteDeepJacobiSubconvexUpTo J q ⌈Real.log (q : ℝ)⌉₊ C) :
    ConcreteDeepJacobiCeilSubconvex J q C :=
  hup ⌈Real.log (q : ℝ)⌉₊ hceil le_rfl

/-- Direct ceiling-depth consumer for the concrete R287 route: a calibrated
R23 rung-3 certificate plus a depth-3-to-ceiling upgrade gives the log-depth
Jacobi-convolution endpoint. -/
theorem concreteDeepJacobiCeilSubconvex_of_concreteRungThree_upgrade
    (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hceil : 3 ≤ ⌈Real.log (q : ℝ)⌉₊)
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade :
      IterConvEnergyWick J q 3 C →
        ConcreteDeepJacobiSubconvexUpTo J q ⌈Real.log (q : ℝ)⌉₊ C)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiCeilSubconvex J q C :=
  concreteDeepJacobiCeilSubconvex_of_upTo J q C hceil
    (concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_upgrade
      J q ⌈Real.log (q : ℝ)⌉₊ hBC hupgrade h3)

/-- A named depth-3-to-ceiling upgrade consumes a calibrated concrete R23
rung-3 certificate directly. -/
theorem concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade
    (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiCeilSubconvex J q C :=
  hupgrade (iterConvEnergyWick_three_of_concreteRungThree J q hBC h3)

/-- Relaxed-constant version of the named endpoint upgrade: a sharper
depth-3 certificate at `C` can feed an endpoint upgrade published at any larger
constant `C'`. -/
theorem concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade_le_const
    (J : ZMod m → ℂ) (q : ℕ) {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C')
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiCeilSubconvex J q C' :=
  hupgrade
    (iterConvEnergyWick_mono_const J q 3 hC0 hCC
      (iterConvEnergyWick_three_of_concreteRungThree J q hBC h3))

/-- Recurrence-only sufficient condition for the concrete log-depth endpoint,
using the R95/R96 head budget `m ≤ 4*C`.  This records exactly what the
available Cauchy propagation proves; an actual prize proof still needs a
depth-3-to-log-depth upgrade that avoids this linear-in-`m` budget. -/
theorem concreteDeepJacobiCeilSubconvex_of_concreteRungThree_left_budget
    (J : ZMod m → ℂ) (q : ℕ) {B C C' : ℝ}
    (hceil : 3 ≤ ⌈Real.log (q : ℝ)⌉₊)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h3 : ConcreteRungThreeSubconvex J q B) :
    ConcreteDeepJacobiCeilSubconvex J q C' :=
  concreteDeepJacobiCeilSubconvex_of_upTo J q C' hceil
    (concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_left_budget
      J q ⌈Real.log (q : ℝ)⌉₊ hJ hC0 hCC hBC hleft h3)

/-- The R95/R96 recurrence budget at a depth-3 head already forces
`C ≥ m/4`.  This is the arithmetic obstruction behind the recurrence-only
baseline. -/
theorem left_budget_forces_const_ge
    {C : ℝ} (hleft : (m : ℝ) ≤ C * (4 : ℝ)) :
    (m : ℝ) / 4 ≤ C := by
  nlinarith

/-- The R95/R96 depth-3 left budget is exactly the lower bound `C ≥ m/4`. -/
theorem left_budget_iff_const_ge {C : ℝ} :
    (m : ℝ) ≤ C * (4 : ℝ) ↔ (m : ℝ) / 4 ≤ C := by
  constructor
  · exact left_budget_forces_const_ge
  · intro hC
    nlinarith

/-- A bounded public constant below `m/4` cannot pay the R95/R96 depth-3
left-budget needed by the recurrence-only route. -/
theorem not_left_budget_of_const_lt
    {C K : ℝ} (hCK : C ≤ K) (hK : K * (4 : ℝ) < (m : ℝ)) :
    ¬ (m : ℝ) ≤ C * (4 : ℝ) := by
  intro hleft
  nlinarith

/-! ## Concrete endpoint to abstract prize-floor consumers -/

/-- A concrete log-depth Jacobi-convolution certificate feeds the abstract
`DeepJacobiSubconvex` route once the caller supplies the concrete-to-abstract
interpretation, the Jacobi-to-hyperplane consumer, and the existing
hyperplane-to-floor consumer. -/
theorem prizeFloor_of_concreteDeepJacobiCeilSubconvex
    (Ω : Type*) (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (hceil : ConcreteDeepJacobiCeilSubconvex J q C) :
    PrizeFloor Ω :=
  hfloor (hjacobi (hdeep hceil))

/-- End-to-end concrete R287 consumer: a calibrated R23 rung-3 certificate,
a depth-3-to-ceiling upgrade, and the concrete-to-abstract interpretation feed
the abstract prize-floor route. -/
theorem prizeFloor_of_concreteRungThree_upgrade
    (Ω : Type*) (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hceil : 3 ≤ ⌈Real.log (q : ℝ)⌉₊)
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade :
      IterConvEnergyWick J q 3 C →
        ConcreteDeepJacobiSubconvexUpTo J q ⌈Real.log (q : ℝ)⌉₊ C)
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    PrizeFloor Ω :=
  prizeFloor_of_concreteDeepJacobiCeilSubconvex Ω J q hdeep hjacobi hfloor
    (concreteDeepJacobiCeilSubconvex_of_concreteRungThree_upgrade
      J q hceil hBC hupgrade h3)

/-- End-to-end R287 consumer from the named concrete endpoint upgrade.  This
is the cleanest statement of the remaining route: prove
`ConcreteDepthThreeToCeilUpgrade` for the concrete Jacobi sequence, then supply
the concrete-to-abstract and hyperplane/floor consumers. -/
theorem prizeFloor_of_concreteRungThree_endpoint_upgrade
    (Ω : Type*) (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C)
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    PrizeFloor Ω :=
  prizeFloor_of_concreteDeepJacobiCeilSubconvex Ω J q hdeep hjacobi hfloor
    (concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade
      J q hBC hupgrade h3)

/-- Relaxed-constant end-to-end consumer from the named concrete endpoint
upgrade.  This lets a sharp rung-3 certificate publish through a larger
campaign Wick constant before entering the abstract prize-floor route. -/
theorem prizeFloor_of_concreteRungThree_endpoint_upgrade_le_const
    (Ω : Type*) (J : ZMod m → ℂ) (q : ℕ) {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hupgrade : ConcreteDepthThreeToCeilUpgrade J q C')
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C' → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    PrizeFloor Ω :=
  prizeFloor_of_concreteDeepJacobiCeilSubconvex Ω J q hdeep hjacobi hfloor
    (concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade_le_const
      J q hC0 hCC hBC hupgrade h3)

/-- End-to-end recurrence-baseline consumer: a calibrated R23 rung-3
certificate reaches the abstract prize-floor route via the R95/R96 Cauchy
propagation, with the linear-in-`m` head budget exposed.  This is a checked
baseline, not the desired prize-scale subconvexity upgrade. -/
theorem prizeFloor_of_concreteRungThree_left_budget
    (Ω : Type*) (J : ZMod m → ℂ) (q : ℕ) {B C C' : ℝ}
    (hceil : 3 ≤ ⌈Real.log (q : ℝ)⌉₊)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hdeep : ConcreteDeepJacobiCeilSubconvex J q C' → DeepJacobiSubconvex Ω)
    (hjacobi : DeepJacobiSubconvex Ω → HyperplaneSubconvex Ω)
    (hfloor : HyperplaneSubconvex Ω → PrizeFloor Ω)
    (h3 : ConcreteRungThreeSubconvex J q B) :
    PrizeFloor Ω :=
  prizeFloor_of_concreteDeepJacobiCeilSubconvex Ω J q hdeep hjacobi hfloor
    (concreteDeepJacobiCeilSubconvex_of_concreteRungThree_left_budget
      J q hceil hJ hC0 hCC hBC hleft h3)

end ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.jacobiPackage_of_rungThree_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.hyperplaneSubconvex_of_jacobiPackage
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_rungThree_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.ConcreteRungThreeSubconvex.mono_const
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.ConcreteDeepJacobiSubconvexUpTo.mono_depth
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.ConcreteDeepJacobiSubconvexUpTo.mono_const
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.ConcreteDeepJacobiCeilSubconvex.mono_const
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.iterConvEnergyWick_three_of_concreteRungThree
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiSubconvexUpTo_of_concreteRungThree_left_budget
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiCeilSubconvex_of_upTo
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiCeilSubconvex_of_concreteRungThree_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiCeilSubconvex_of_concreteRungThree_endpoint_upgrade_le_const
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.concreteDeepJacobiCeilSubconvex_of_concreteRungThree_left_budget
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.left_budget_forces_const_ge
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.left_budget_iff_const_ge
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.not_left_budget_of_const_lt
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_concreteDeepJacobiCeilSubconvex
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_concreteRungThree_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_concreteRungThree_endpoint_upgrade
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_concreteRungThree_endpoint_upgrade_le_const
#print axioms
  ProximityGap.Frontier.R287JacobiConvolutionSubconvexitySocket.prizeFloor_of_concreteRungThree_left_budget
