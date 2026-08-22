/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R95IterConvMultiStepPublicConstantConsumers

/-!
# LANE B2 (#466 round 96): monotone budget adapters for multi-step Wick propagation

R95 propagates Wick certificates over a window of successor depths under the explicit budget

`∀ t ∈ [r, r+k), (m : ℝ) ≤ C * (t+1)`.

For nonnegative `C`, that budget is monotone in `t`.  Thus the whole window is paid by the
left endpoint `(m : ℝ) ≤ C * (r+1)`.  This file packages that elementary reduction and exposes
the corresponding R95 consumers with a single left-end budget hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R66TripleConvIterWickAdapter
open ArkLib.ProximityGap.Frontier.R91PointwiseTripleToIterWickBridge
open ArkLib.ProximityGap.Frontier.R95IterConvMultiStepPublicConstantConsumers

variable {m : ℕ} [NeZero m]

/-- For nonnegative Wick constant `C`, the R95 window budget is discharged by its left endpoint. -/
theorem iterConvBudget_window_of_left
    {r k : ℕ} {C : ℝ}
    (hC0 : 0 ≤ C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    ∀ t : ℕ, r ≤ t → t < r + k →
      (m : ℝ) ≤ C * ((t + 1 : ℕ) : ℝ) := by
  intro t hrt _ht
  have hnat : r + 1 ≤ t + 1 := Nat.succ_le_succ hrt
  have hreal : ((r + 1 : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hleft.trans (mul_le_mul_of_nonneg_left hreal hC0)

/-- Multi-step Wick propagation from a previous certificate, with the whole budget window
collapsed to the left-end inequality. -/
theorem iterConvEnergyWick_add_of_prev_of_left_budget
    (J : ZMod m → ℂ) (q r k : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C)
    (hprev : IterConvEnergyWick J q r C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + k) C :=
  iterConvEnergyWick_add_of_prev_of_budget J q r k hJ hC0 hprev
    (iterConvBudget_window_of_left hC0 hleft)

/-- Multi-step Wick propagation at a larger public constant, with a single left-end budget. -/
theorem iterConvEnergyWick_add_of_prev_of_left_budget_le_const
    (J : ZMod m → ℂ) (q r k : ℕ) {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J q r C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + k) C' :=
  iterConvEnergyWick_add_of_prev_of_budget_le_const J q r k hJ hC0 hCC hprev
    (iterConvBudget_window_of_left hC0 hleft)

/-- Universal-depth form of the left-end budget adapter: once a rung `r` is certified and the
left endpoint pays for the successor window, every later depth has the same Wick constant. -/
theorem iterConvEnergyWick_of_ge_of_prev_of_left_budget
    (J : ZMod m → ℂ) (q r s : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C)
    (hprev : IterConvEnergyWick J q r C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    (hrs : r ≤ s) :
    IterConvEnergyWick J q s C := by
  simpa [Nat.add_sub_of_le hrs] using
    (iterConvEnergyWick_add_of_prev_of_left_budget
      (m := m) J q r (s - r) hJ hC0 hprev hleft)

/-- Universal-depth form at a larger public constant. -/
theorem iterConvEnergyWick_of_ge_of_prev_of_left_budget_le_const
    (J : ZMod m → ℂ) (q r s : ℕ) {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J q r C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    (hrs : r ≤ s) :
    IterConvEnergyWick J q s C' := by
  simpa [Nat.add_sub_of_le hrs] using
    (iterConvEnergyWick_add_of_prev_of_left_budget_le_const
      (m := m) J q r (s - r) hJ hC0 hCC hprev hleft)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Universal-depth face-moment consumer for the left-end budget adapter.  Once a rung `r` is
certified and the left endpoint pays the successor budget, every later depth can be published
directly as a pure-face moment bound. -/
theorem sup_pureFace_of_ge_of_iterConvEnergyWick_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {r s : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J (Fintype.card F) r C)
    (hleft : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    (hrs : r ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace J lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_of_ge_of_prev_of_left_budget_le_const
      J (Fintype.card F) r s hJ hC0 hCC hprev hleft hrs)
    hx

/-- Calibrated r = 3 energy input propagated to depth `3+k`, with the R95 budget window
reduced to the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem iterConvEnergyWick_from_three_of_tripleConvEnergyBound_left_budget_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : TripleConvEnergyBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvEnergyBound_le_const J q k
    hJ hC0 hCC hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    h

/-- Calibrated r = 3 energy input propagated to every depth `s ≥ 3`, with the R95 budget
window reduced to the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem iterConvEnergyWick_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const
    (J : ZMod m → ℂ) (q s : ℕ) {B C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : TripleConvEnergyBound J q B)
    (hs : 3 ≤ s) :
    IterConvEnergyWick J q s C' := by
  simpa [Nat.add_sub_of_le hs] using
    (iterConvEnergyWick_from_three_of_tripleConvEnergyBound_left_budget_le_const
      (m := m) J q (s - 3) hJ hC0 hCC hBC hleft h)

/-- Calibrated r = 3 energy input propagated to every depth `s ≥ 3` and consumed directly by
the pure-face moment bound, with only the left-end budget `(m : ℝ) ≤ 4*C`. -/
theorem sup_pureFace_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : TripleConvEnergyBound J (Fintype.card F) B)
    (hs : 3 ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace J lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_of_ge_of_iterConvEnergyWick_left_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvEnergyBound
      J (Fintype.card F) hBC h)
    (by simpa using hleft)
    hs hx

/-- Calibrated r = 3 energy input propagated and consumed by the face-moment bound, with the
whole budget window collapsed to `(m : ℝ) ≤ 4*C`. -/
theorem sup_pureFace_from_three_of_tripleConvEnergyBound_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : TripleConvEnergyBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_from_three_of_tripleConvEnergyBound_le_const hfam hgrp J k
    hJ hC0 hCC hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    h hs

/-- Energy-level expanded Jacobi Hermitian input propagated to depth `3+k`, with the R95
budget window reduced to the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_left_budget_le_const
    {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvEnergyBound_left_budget_le_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) k
    hJ hC0 hCC hBC hleft
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h)

/-- Energy-level expanded Jacobi Hermitian input propagated to every depth `s ≥ 3`, with the
R95 budget window reduced to the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_ge_left_budget_le_const
    {B C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B)
    (hs : 3 ≤ s) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) s C' := by
  simpa [Nat.add_sub_of_le hs] using
    (iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_left_budget_le_const
      (m := m) (F := F) (lam := lam) (χ := χ) (s - 3)
      hJ hC0 hCC hBC hleft h)

/-- Energy-level expanded Jacobi Hermitian input propagated and consumed by the face-moment
bound, with the whole budget window collapsed to `(m : ℝ) ≤ 4*C`. -/
theorem sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_from_three_of_tripleConvEnergyBound_left_budget_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i) k
    hJ hC0 hCC hBC hleft
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h) hs

/-- Energy-level expanded Jacobi Hermitian input propagated to every depth `s ≥ 3` and
consumed directly by the face-moment bound, with only the left-end Wick budget. -/
theorem sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_ge_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBC : B ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiAdditiveTripleHermitianExpandedEnergyBound χ lam B)
    (hs : 3 ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i) s
    hJ hC0 hCC hBC hleft
    ((jacobiAdditiveTripleHermitianExpandedEnergyBound_iff_tripleConvEnergyBound
      (χ := χ) (lam := lam) (C := B)).mp h)
    hs hx

/-- Pointwise r = 3 input propagated to depth `3+k`, with the R95 budget window reduced to
the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const
    (J : ZMod m → ℂ) (q k : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const J q k
    hJ hC0 hCC hBB hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    hpt

/-- Pointwise r = 3 input checked at a smaller ambient parameter, propagated to depth `3+k`
at a larger ambient parameter with only the left-end Wick budget. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} (k : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q' : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B) :
    IterConvEnergyWick J q' (3 + k) C' :=
  iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_le_const_q J k
    hJ hC0 hCC hqq hBB hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    hpt

/-- Pointwise r = 3 input propagated to every depth `s ≥ 3`, with only the left-end Wick
budget. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const
    (J : ZMod m → ℂ) (q s : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B)
    (hs : 3 ≤ s) :
    IterConvEnergyWick J q s C' := by
  simpa [Nat.add_sub_of_le hs] using
    (iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const
      (m := m) J q (s - 3) hJ hC0 hCC hBB hBC hleft hpt)

/-- Pointwise r = 3 input checked at a smaller ambient parameter and propagated to every
depth `s ≥ 3` at a larger ambient parameter, with only the left-end Wick budget. -/
theorem iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const_q
    (J : ZMod m → ℂ) {q q' : ℕ} (s : ℕ) {B B' C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q' : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B)
    (hs : 3 ≤ s) :
    IterConvEnergyWick J q' s C' := by
  simpa [Nat.add_sub_of_le hs] using
    (iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const_q
      (m := m) J (s - 3) hJ hC0 hCC hqq hBB hBC hleft hpt)

/-- Pointwise r = 3 input propagated to every depth `s ≥ 3` and consumed directly by the
pure-face moment bound, with only the left-end Wick budget. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B)
    (hs : 3 ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace J lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const hfam hgrp J s
    hJ hC0 hCC hBC hleft
    (tripleConvEnergyBound_of_pointwise J (Fintype.card F)
      (fun d => (hpt d).trans (by
        have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
        have hq : 0 ≤ (Fintype.card F : ℝ) ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBB hm) hq)))
    hs hx

/-- Pointwise r = 3 input checked at a smaller ambient parameter, propagated to every depth
`s ≥ 3`, and consumed directly by the pure-face moment bound. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B B' C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B)
    (hs : 3 ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace J lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const_q
      J s hJ hC0 hCC hqq hBB hBC hleft hpt hs)
    hx

/-- Pointwise r = 3 input propagated to depth `3+k` and consumed by the face-moment bound,
with the R95 budget window reduced to the head inequality `(m : ℝ) ≤ 4*C`. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J (Fintype.card F) B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_add_of_iterConvEnergyWick_prev_of_budget_le_const hfam hgrp J
    hJ hC0 hCC
    (iterConvEnergyWick_three_of_tripleConvPointwiseBound_le J (Fintype.card F)
      hBB hBC hpt)
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    hs

/-- Pointwise r = 3 input checked at a smaller ambient parameter, propagated to depth `3+k`,
and consumed by the face-moment bound with only the left-end Wick budget. -/
theorem sup_pureFace_from_three_of_tripleConvPointwiseBound_left_budget_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q : ℕ} {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (hpt : TripleConvPointwiseBound J q B) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_from_three_of_tripleConvPointwiseBound_le_const_q hfam hgrp J k
    hJ hC0 hCC hqq hBB hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    hpt hs

/-- Jacobi six-input propagation to depth `3+k`, with only the left-end Wick budget. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_left_budget_le_const
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiHermitianSixInput χ lam B) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) (3 + k) C' :=
  iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_le_const
    (m := m) (F := F) (lam := lam) (χ := χ) k
    hJ hC0 hCC hBB hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    h

/-- Jacobi six-input propagation to every depth `s ≥ 3`, with only the left-end Wick budget. -/
theorem iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_ge_left_budget_le_const
    {B B' C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiHermitianSixInput χ lam B)
    (hs : 3 ≤ s) :
    IterConvEnergyWick
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) s C' := by
  simpa [Nat.add_sub_of_le hs] using
    (iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_left_budget_le_const
      (m := m) (F := F) (lam := lam) (χ := χ) (s - 3)
      hJ hC0 hCC hBB hBC hleft h)

/-- Jacobi six-input propagation to every depth `s ≥ 3` and face-moment consumption, with
only the left-end Wick budget. -/
theorem sup_pureFace_from_three_of_jacobiHermitianSixInput_ge_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ} (s : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiHermitianSixInput χ lam B)
    (hs : 3 ≤ s) {x : F} (hx : x ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam x‖ ^ (2 * s)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ s * (s.factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ s) :=
  sup_pureFace_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const hfam hgrp
    (fun i : ZMod m => jacobiCoeff χ lam i) s
    hJ hC0 hCC hBB hBC hleft
    ((jacobiHermitianSixInput_iff_tripleConvPointwiseBound
      (χ := χ) (lam := lam) (C := B)).mp h)
    hs hx

/-- Jacobi six-input propagation and face-moment consumption, with the whole budget window
collapsed to `(m : ℝ) ≤ 4*C`. -/
theorem sup_pureFace_from_three_of_jacobiHermitianSixInput_left_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' C C' : ℝ} (k : ℕ)
    (hJ : ∀ j : ZMod m, ‖jacobiCoeff χ lam j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hBB : B ≤ B')
    (hBC : B' ≤ C ^ 3 * ((Nat.factorial 3 : ℕ) : ℝ))
    (hleft : (m : ℝ) ≤ C * (4 : ℝ))
    (h : JacobiHermitianSixInput χ lam B) {s : F} (hs : s ≠ 0) :
    ‖pureFace (fun i : ZMod m => jacobiCoeff χ lam i) lam s‖ ^ (2 * (3 + k))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (3 + k) * ((3 + k).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (3 + k)) :=
  sup_pureFace_from_three_of_jacobiHermitianSixInput_le_const
    (m := m) (F := F) (lam := lam) (G := G) (χ := χ) hfam hgrp k
    hJ hC0 hCC hBB hBC
    (by
      simpa using
        (iterConvBudget_window_of_left (m := m) (r := 3) (k := k) (C := C)
          hC0 (by simpa using hleft)))
    h hs

end ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvBudget_window_of_left
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_add_of_prev_of_left_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_add_of_prev_of_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_of_ge_of_prev_of_left_budget
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_of_ge_of_prev_of_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_of_ge_of_iterConvEnergyWick_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvEnergyBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvEnergyBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvEnergyBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_jacobiHermitianExpandedEnergyBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_jacobiHermitianExpandedEnergyBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_left_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvPointwiseBound_ge_left_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvPointwiseBound_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_tripleConvPointwiseBound_left_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.iterConvEnergyWick_from_three_of_jacobiHermitianSixInput_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_jacobiHermitianSixInput_ge_left_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R96IterConvBudgetMonotoneAdapters.sup_pureFace_from_three_of_jacobiHermitianSixInput_left_budget_le_const
