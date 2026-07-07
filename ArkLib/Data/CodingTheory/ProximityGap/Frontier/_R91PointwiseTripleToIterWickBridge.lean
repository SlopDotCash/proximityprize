/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R66TripleConvIterWickAdapter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R88TripleConvConstantAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R90IterConvWickConstantAdapters

/-!
# LANE B2 (#466 round 91): pointwise r = 3 certificates feed the full Wick ladder

R26 names the local Katz-style target `TripleConvPointwiseBound`; R23 consumes it as the calibrated
sextic energy input; R66 identifies that input with the r = 3 instance of `IterConvEnergyWick`.
This file composes those steps once, including a public-constant relaxation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters

variable {m : ℕ} [NeZero m]

/-- A pointwise r = 3 certificate at a sharp constant `B` feeds the full-tower
`IterConvEnergyWick` r = 3 interface at any Wick constant `C` whose normalization dominates a
published intermediate constant `B'`. -/
theorem iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
    (J : ZMod m → ℂ) (q : ℕ) {B B' C : ℝ}
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q 3 C :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC
    (tripleConvEnergyBound_of_pointwise_le J q hBB hpt)

/-- Direct public-constant form: a pointwise r = 3 certificate at constant `B` feeds
`IterConvEnergyWick` r = 3 when `B <= 6*C^3`. -/
theorem iterConvEnergyWick_three_of_tripleConvPointwiseBound
    (J : ZMod m → ℂ) (q : ℕ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q 3 C :=
  iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J q (le_rfl : B ≤ B) hBC hpt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F}

/-- Pointwise r = 3 cancellation directly supplies the full-tower pointwise face bound at depth
three. -/
theorem sup_pureFace_three_of_tripleConvPointwiseBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C : ℝ}
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * 3)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
      J (Fintype.card F) hBB hBC hpt) hs

/-- Direct public-constant face-bound form at depth three. -/
theorem sup_pureFace_three_of_tripleConvPointwiseBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * 3)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvPointwiseBound_le hfam hgrp J
    (le_rfl : B ≤ B) hBC hpt hs

end ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge.iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
#print axioms
  ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge.iterConvEnergyWick_three_of_tripleConvPointwiseBound
#print axioms
  ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge.sup_pureFace_three_of_tripleConvPointwiseBound_le
