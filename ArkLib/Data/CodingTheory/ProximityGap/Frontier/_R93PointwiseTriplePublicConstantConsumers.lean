/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R92JacobiHermitianSixIterWickConsumers

/-!
# LANE B2 (#466 round 93): pointwise r = 3 certificates with public Wick constants

R91 consumes a pointwise triple-convolution certificate at Wick constant `C`.  R90 supplies
monotonicity in the published `IterConvEnergyWick` constant.  This file records the composed
public-constant wrappers, including the Jacobi Hermitian six-input surface from R92.

The point is small but practical: a sharp local certificate can be checked at `C` and published at
any larger campaign constant `C'` without reopening the r = 3 tower arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters
open ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge
open ArkLib.ProximityGap.Frontier.R92JacobiHermitianSixIterWickConsumers

variable {m : ℕ} [NeZero m]

/-- Pointwise r = 3 cancellation feeds the third full-tower Wick rung at any larger published
Wick constant. -/
theorem iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
    (J : ZMod m → ℂ) (q : ℕ) {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q 3 C' :=
  iterConvEnergyWick_mono_const J q 3 hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J q hBB hBC hpt)

/-- Pointwise r = 3 cancellation at a smaller ambient parameter feeds the third full-tower
Wick rung at any larger ambient parameter and any larger published Wick constant. -/
theorem iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q' 3 C' :=
  iterConvEnergyWick_mono_q J (le_trans hC0 hCC) hqq
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
      J q hC0 hCC hBB hBC hpt)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Pointwise r = 3 cancellation feeds the third face-moment consumer at any larger published
Wick constant. -/
theorem sup_pureFace_three_of_tripleConvPointwiseBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) := by
  simpa using
    sup_pureFace_of_iterConvEnergyWick_le_const
      (F := F) (m := m) (lam := lam) (G := G)
      hfam hgrp J hC0 hCC
      (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J (Fintype.card F) hBB hBC hpt)
      hs

/-- Pointwise r = 3 cancellation at any `q ≤ |F|` feeds the actual finite-field
third face-moment consumer at any larger published Wick constant. -/
theorem sup_pureFace_three_of_tripleConvPointwiseBound_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) := by
  simpa using
    sup_pureFace_of_iterConvEnergyWick_le_const_q
      (F := F) (m := m) (lam := lam) (G := G)
      hfam hgrp J hC0 hCC hqq
      (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J q hBB hBC hpt)
      hs

/-- Jacobi Hermitian six-input feeds the third full-tower Wick rung at any larger published
Wick constant. -/
theorem iterConvEnergyWick_three_of_jacobiHermitianSixInput_le_const
    {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C' :=
  iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
    hC0 hCC hBB hBC
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- Jacobi Hermitian six-input feeds the third face-moment consumer at any larger published
Wick constant. -/
theorem sup_pureFace_three_of_jacobiHermitianSixInput_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvPointwiseBound_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    hC0 hCC hBB hBC
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

end ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.sup_pureFace_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.sup_pureFace_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.iterConvEnergyWick_three_of_jacobiHermitianSixInput_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers.sup_pureFace_three_of_jacobiHermitianSixInput_le_const
