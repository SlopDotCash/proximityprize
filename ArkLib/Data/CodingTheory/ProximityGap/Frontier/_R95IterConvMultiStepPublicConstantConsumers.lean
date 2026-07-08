/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R93PointwiseTriplePublicConstantConsumers
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R94IterConvSuccPublicConstantAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R66TripleConvIterWickAdapter

/-!
# LANE B2 (#466 round 95): multi-step Wick propagation from the r = 3 head

R94 exposes the one-step Wick recursion at a larger public constant.  This file iterates that
recursion.  The honest mathematical payload is the budget predicate

`∀ t ∈ [r, r+k), (m : ℝ) ≤ C * (t+1)`.

Thus a future proof that the Jacobi head rungs can pay those factors lands directly as a deep
`IterConvEnergyWick` certificate, and a pointwise r = 3 / Jacobi six-input certificate can be
propagated to any target depth `3+k` under exactly those explicit head-rung budgets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters
open ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge
open ArkLib.ProximityGap.Frontier.R93PointwiseTriplePublicConstantConsumers
open ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters

variable {m : ℕ} [NeZero m]

/-- Iterated Wick propagation over `k` successor steps, with the exact head-rung budget exposed
for each intermediate depth `t ∈ [r, r+k)`. -/
theorem iterConvEnergyWick_add_of_prev_of_budget
    (J : ZMod m → ℂ) (q r k : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C)
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + k) C := by
  induction k with
  | zero =>
      simpa using hprev
  | succ k ih =>
      have hprevk : IterConvEnergyWick J q (r + k) C := by
        apply ih
        intro t hrt htk
        exact hbudget t hrt (by omega)
      have hstepBudget : (m : ℝ) ≤ C * (((r + k) + 1 : ℕ) : ℝ) :=
        hbudget (r + k) (by omega) (by omega)
      simpa [Nat.add_assoc] using
        iterConvEnergyWick_succ_of_prev_of_budget J q (r + k) hJ hC0 hprevk hstepBudget

/-- Multi-step Wick propagation, published at any larger public constant. -/
theorem iterConvEnergyWick_add_of_prev_of_budget_le_const
    (J : ZMod m → ℂ) (q r k : ℕ) {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + k) C' :=
  iterConvEnergyWick_mono_const J q (r + k) hC0 hCC
    (iterConvEnergyWick_add_of_prev_of_budget J q r k hJ hC0 hprev hbudget)

/-- Multi-step Wick propagation, published at any larger public constant and ambient size. -/
theorem iterConvEnergyWick_add_of_prev_of_budget_le_const_q
    (J : ZMod m → ℂ) {q q' r k : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q' : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q' (r + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q' r k hJ hC0 hCC
    (iterConvEnergyWick_mono_q J hC0 hqq hprev)
    hbudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Multi-step Wick propagation, immediately consumed by the pointwise face bound at the larger
public constant. -/
theorem sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {r k : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J (Fintype.card F) r C)
    (hbudget : ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (r + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (r + k) * ((r + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (r + k)) :=
  sup_pureFace_of_iterConvEnergyWick_le_const
    (F := F) (m := m) (lam := lam) (G := G)
    hfam hgrp J hC0 hCC
    (iterConvEnergyWick_add_of_prev_of_budget J (Fintype.card F) r k
      hJ hC0 hprev hbudget)
    hs

/-- Multi-step Wick propagation at a smaller ambient parameter, immediately consumed by the
pointwise face bound at the actual field size. -/
theorem sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q r k : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (r + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (r + k) * ((r + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (r + k)) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_add_of_prev_of_budget_le_const
      J (Fintype.card F) r k hJ hC0 hCC
      (iterConvEnergyWick_mono_q J hC0 hqq hprev)
      hbudget)
    hs

/-- A calibrated r = 3 energy certificate propagates to depth `3+k` under the explicit
head-rung budgets, and can be published at any larger Wick constant. -/
theorem iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q 3 k hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)
    hbudget

/-- A calibrated r = 3 energy certificate checked at a smaller ambient parameter propagates to
depth `3+k` at any larger ambient parameter. -/
theorem iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} (k : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q' : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q' (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const_q J (q := q) (q' := q') (r := 3) (k := k)
    hJ hC0 hCC hqq
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)
    hbudget

/-- A calibrated r = 3 energy certificate propagates to depth `3+k` under explicit head-rung
budgets, then feeds the public face-moment bound. -/
theorem sup_pureFace_from_three_of_tripleConvEnergyBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J (Fintype.card F) hBC h)
    hbudget hs

/-- A calibrated r = 3 energy certificate checked at a smaller ambient parameter propagates to
depth `3+k`, then feeds the public face-moment bound at the field-size ambient parameter. -/
theorem sup_pureFace_from_three_of_tripleConvEnergyBound_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : TripleConvEnergyBound J q B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const_q hfam hgrp J
    hJ hC0 hCC hqq
    (iterConvEnergyWick_three_of_tripleConvEnergyBound J q hBC h)
    hbudget hs

/-- Energy-level expanded Jacobi Hermitian input propagates to depth `3+k` under the explicit
head-rung budgets, and can be published at any larger Wick constant. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_le_const
    {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) k
    hJ hC0 hCC hBC hbudget
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- Energy-level expanded Jacobi Hermitian input propagates to depth `3+k` and feeds the public
face-moment bound. -/
theorem sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_from_three_of_tripleConvEnergyBound_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i) k
    hJ hC0 hCC hBC hbudget
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

/-- A pointwise r = 3 certificate propagates to depth `3+k` under the explicit head-rung
budgets, and can be published at any larger Wick constant. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q 3 k hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J q hBB hBC hpt)
    hbudget

/-- A pointwise r = 3 certificate checked at a smaller ambient parameter `q` propagates to
depth `3+k` at any larger ambient parameter `q'`, under the same explicit head-rung budgets. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} (k : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q' : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q' (3 + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q' 3 k hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const_q
      J hC0 le_rfl hqq hBB hBC hpt)
    hbudget

/-- A pointwise r = 3 certificate propagates to depth `3+k` under explicit head-rung budgets,
then feeds the public face-moment bound. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J (Fintype.card F)
      hBB hBC hpt)
    hbudget hs

/-- A pointwise r = 3 certificate checked at a smaller ambient parameter propagates to depth
`3+k` and feeds the public face-moment bound at the field-size ambient parameter. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (hpt : TripleConvPointwiseBound J q B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le_const_q
      J hC0 le_rfl hqq hBB hBC hpt)
    hbudget hs

/-- Jacobi six-input propagation from the r = 3 head to depth `3+k`, under exactly the explicit
head-rung budgets. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_le_const
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) k
    hJ hC0 hCC hBB hBC hbudget
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- Jacobi six-input propagation from the r = 3 head, immediately consumed by the public
face-moment bound at depth `3+k`. -/
theorem sup_pureFace_from_three_of_jacobiHermitianSixInput_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hbudget : ∀ t : ℕ, 3 ≤ t → t < 3 + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ))
    (h : JacobiHermitianSixInput χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i)
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F)
      hBB hBC
      ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
        (χ := χ) (lam := lam) (C := B)).mp h))
    hbudget hs

end ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_add_of_prev_of_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_add_of_prev_of_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_add_of_prev_of_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_tripleConvEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_tripleConvEnergyBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_tripleConvPointwiseBound_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_tripleConvPointwiseBound_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers.sup_pureFace_from_three_of_jacobiHermitianSixInput_le_const
