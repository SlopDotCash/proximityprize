/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R66TripleConvIterWickAdapter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26PointwiseTripleConvTarget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R90IterConvWickConstantAdapters

/-!
# LANE B2 (#466 round 91): r = 3 triple-convolution certificates as public Wick consumers

R66 identifies the calibrated R23 `TripleConvEnergyBound` with the third rung of the full
`IterConvEnergyWick` tower.  R90 adds monotonicity in the published Wick constant.  This file
composes those two interfaces so that a sharp sextic/triple-convolution certificate can be consumed
directly at any larger public full-tower constant, and then by the pointwise sup consumer.

This is still interface plumbing around the `r = 3` face, not the deep `r ≈ log q` prize wall.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters

variable {m : ℕ} [NeZero m]

/-- A calibrated triple-convolution certificate gives the third full-tower Wick rung at any
larger published tower constant. -/
theorem iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const
    (J : ZMod m → ℂ) (q : ℕ) {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q 3 C' :=
  iterConvEnergyWick_mono_const J q 3 hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)

theorem iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q' 3 C' :=
  iterConvEnergyWick_mono_const_q J hC0 hCC hqq
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F}

/-- A calibrated triple-convolution certificate can be consumed directly by the pointwise
third-moment face bound at any larger public tower constant. -/
theorem sup_pureFace_three_of_tripleConvEnergyBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) := by
  simpa using
    sup_pureFace_of_iterConvEnergyWick_le_const
      (F := F) (m := m) (lam := lam) (G := G)
      hfam hgrp J hC0 hCC
      (iterConvEnergyWick_three_of_tripleConvEnergyBound J (Fintype.card F) hBC h)
      hs

/-- Field-size-parametric version of
`sup_pureFace_three_of_tripleConvEnergyBound_le_const`: a triple-convolution certificate at any
`q ≤ |F|` feeds the actual finite-field face bound. -/
theorem sup_pureFace_three_of_tripleConvEnergyBound_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) := by
  simpa using
    sup_pureFace_of_iterConvEnergyWick_le_const_q
      (F := F) (m := m) (lam := lam) (G := G)
      hfam hgrp J hC0 hCC hqq
      (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)
      hs

/-- A pointwise triple-convolution certificate gives the third full-tower Wick rung at any
larger public tower constant. -/
theorem iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
    (J : ZMod m → ℂ) (q : ℕ) {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q 3 C' :=
  iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const J q hC0 hCC hBC
    (tripleConvEnergyBound_of_pointwise J q
      (fun d => (hpt d).trans (by
        have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
        have hq : 0 ≤ (q : ℝ) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBB hm) hq)))

/-- Field-size-parametric pointwise version: a pointwise triple-convolution certificate at
`q ≤ q'` gives the third full-tower Wick rung at `q'` and any larger public tower constant. -/
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

/-- A pointwise triple-convolution certificate can be consumed directly by the pointwise
third-moment face bound at any larger public tower constant. -/
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
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvEnergyBound_le_const hfam hgrp J hC0 hCC hBC
    (tripleConvEnergyBound_of_pointwise J (Fintype.card F)
      (fun d => (hpt d).trans (by
        have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
        have hq : 0 ≤ (Fintype.card F : ℝ) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBB hm) hq)))
    hs

/-- Field-size-parametric pointwise version of
`sup_pureFace_three_of_tripleConvPointwiseBound_le_const`: a pointwise certificate at any
`q ≤ |F|` feeds the actual finite-field face bound. -/
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
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_tripleConvEnergyBound_le_const_q hfam hgrp J
    hC0 hCC hqq hBC
    (tripleConvEnergyBound_of_pointwise J q
      (fun d => (hpt d).trans (by
        have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
        have hq : 0 ≤ (q : ℝ) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBB hm) hq)))
    hs

variable {χ : F → ℂ}

/-- At the calibrated constant, the expanded Jacobi Hermitian energy target is exactly the
third full-tower Wick rung.  This is the constant-preserving two-sided version of the r = 3
consumer: no public-constant inflation and no endpoint propagation are involved. -/
theorem jacobiHermitianExpandedEnergyBound_iff_iterConvEnergyWick_three
    {C : ℝ} :
    JacobiAdditiveTripleHermitianExpandedEnergyBound
        χ lam (C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
      ↔ IterConvEnergyWick
        (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C := by
  rw [jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound]
  exact tripleConvEnergyBound_iff_iterConvEnergyWick_three
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)

/-- Energy-level expanded Jacobi Hermitian input gives the third full-tower Wick rung at any
larger public tower constant. -/
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

/-- Energy-level expanded Jacobi Hermitian input feeds the public sixth-power face bound at the
third rung. -/
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
    (fun i : ZMod m => jacobiCoeff χ lam i) hC0 hCC hBC
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

/-- Fully expanded pointwise Jacobi Hermitian input gives the third full-tower Wick rung at
any larger public tower constant. -/
theorem iterConvEnergyWick_three_of_jacobiHermitianExpandedPointwiseBound_le_const
    {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) 3 C' :=
  iterConvEnergyWick_three_of_jacobiHermitianExpandedEnergyBound_le_const
    hC0 hCC hBC
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise_le hBB h)

/-- Fully expanded pointwise Jacobi Hermitian input feeds the public sixth-power face bound
at the third rung. -/
theorem sup_pureFace_three_of_jacobiHermitianExpandedPointwiseBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedPointwiseBound χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ 3) :=
  sup_pureFace_three_of_jacobiHermitianExpandedEnergyBound_le_const hfam hgrp
    hC0 hCC hBC
    (jacobiAdditiveTripleHermitianExpandedEnergyBound_of_pointwise_le hBB h) hs

/-- Jacobi six-input pointwise certificate gives the third full-tower Wick rung at any larger
public tower constant. -/
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

/-- Jacobi six-input pointwise certificate feeds the public sixth-power face bound at the third
rung. -/
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

end ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_tripleConvEnergyBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_tripleConvEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_tripleConvEnergyBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.jacobiHermitianExpandedEnergyBound_iff_iterConvEnergyWick_three
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_jacobiHermitianExpandedEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_jacobiHermitianExpandedEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_jacobiHermitianExpandedPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_jacobiHermitianExpandedPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.iterConvEnergyWick_three_of_jacobiHermitianSixInput_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R91TripleConvIterWickConstantConsumers.sup_pureFace_three_of_jacobiHermitianSixInput_le_const
