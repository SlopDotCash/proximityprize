/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R91PointwiseTripleToIterWickBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R91TripleConvIterWickConstantConsumers

/-!
# LANE B2 (#466 round 92): Jacobi Hermitian six-input as r = 3 Wick consumers

R26 names the fully expanded Jacobi six-variable Hermitian target, and proves that it is exactly
the pointwise triple-convolution target for the Jacobi coefficient sequence.  The R91 bridges then
consume pointwise or energy-level triple-convolution certificates as the third rung of the full
`IterConvEnergyWick` tower.

This file exposes the Jacobi-facing wrappers directly, so a future Katz/Weil certificate for the
expanded six-variable form can land in the r = 3 tower without unfolding the generic interfaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge
open ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The named Jacobi six-variable pointwise input feeds the third full-tower Wick rung. -/
theorem iterConvEnergyWick_three_of_jacobiHermitianSixInput
    {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C :=
  iterConvEnergyWick_three_of_tripleConvPointwiseBound
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) hBC
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- The named Jacobi six-variable pointwise input feeds the third face-moment consumer. -/
theorem sup_pureFace_three_of_jacobiHermitianSixInput
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B C : ℝ}
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * 3)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvPointwiseBound hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i) hBC
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

/-- The energy-level expanded Jacobi Hermitian target feeds the third full-tower Wick rung at
any larger published tower constant. -/
theorem iterConvEnergyWick_three_of_jacobiHermitianExpandedEnergyBound_le_const
    {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C' :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
    hC0 hCC hBC
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- The energy-level expanded Jacobi Hermitian target feeds the third face-moment consumer at
any larger published tower constant. -/
theorem sup_pureFace_three_of_jacobiHermitianExpandedEnergyBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvEnergyBound_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    hC0 hCC hBC
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

end ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers.iterConvEnergyWick_three_of_jacobiHermitianSixInput
#print axioms
  ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers.sup_pureFace_three_of_jacobiHermitianSixInput
#print axioms
  ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers.iterConvEnergyWick_three_of_jacobiHermitianExpandedEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers.sup_pureFace_three_of_jacobiHermitianExpandedEnergyBound_le_const
