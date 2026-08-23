/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30IterConvEnergyRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R90IterConvWickConstantAdapters

/-!
# LANE B2 (#466 round 94): one-step Wick recursion with public constants

R30 proves the formal one-step recursion for the deep iterated-convolution tower: if rung `r`
is at Wick constant `C` and the leftover budget `m ≤ C·(r+1)` is available, then rung `r+1`
is also at constant `C`.

R90 proves monotonicity in the published Wick constant.  This file composes the two, exposing the
successor rung at any larger public constant `C'`.  It is a convenience surface for future partial
deep-rung arguments: the arithmetic budget is checked at the sharp internal constant, while the
campaign-facing theorem may publish a relaxed one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse
open ArkLib.ProximityGap.Frontier.R30IterConvEnergyRecursion
open ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters

variable {m : ℕ} [NeZero m]

/-- One-step Wick propagation, published at any larger public constant. -/
theorem iterConvEnergyWick_succ_of_prev_of_budget_le_const
    (J : ZMod m → ℂ) (q r : ℕ) {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q (r + 1) C' :=
  iterConvEnergyWick_mono_const J q (r + 1) hC0 hCC
    (iterConvEnergyWick_succ_of_prev_of_budget J q r hJ hC0 hprev hbudget)

/-- One-step Wick propagation, published at any larger public constant and ambient size. -/
theorem iterConvEnergyWick_succ_of_prev_of_budget_le_const_q
    (J : ZMod m → ℂ) {q q' r : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ)) :
    IterConvEnergyWick J q' (r + 1) C' :=
  iterConvEnergyWick_mono_q J (le_trans hC0 hCC) hqq
    (iterConvEnergyWick_succ_of_prev_of_budget_le_const
      J q r hJ hC0 hCC hprev hbudget)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F}

/-- One-step Wick propagation, immediately consumed by the pointwise face bound at the larger
public constant. -/
theorem sup_pureFace_succ_of_iterConvEnergyWick_prev_of_budget_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {r : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (Fintype.card F : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (hprev : IterConvEnergyWick J (Fintype.card F) r C)
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (r + 1))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (r + 1) * ((r + 1).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (r + 1)) :=
  sup_pureFace_of_iterConvEnergyWick_le_const
    (F := F) (m := m) (lam := lam) (G := G)
    hfam hgrp J hC0 hCC
    (iterConvEnergyWick_succ_of_prev_of_budget J (Fintype.card F) r
      hJ hC0 hprev hbudget)
    hs

/-- One-step Wick propagation at a smaller ambient size, consumed by the pointwise face bound at
the actual field size and larger public constant. -/
theorem sup_pureFace_succ_of_iterConvEnergyWick_prev_of_budget_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q r : ℕ} {C C' : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ))
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (hprev : IterConvEnergyWick J q r C)
    (hbudget : (m : ℝ) ≤ C * ((r + 1 : ℕ) : ℝ))
    {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * (r + 1))
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ (r + 1) * ((r + 1).factorial : ℝ)
            * ((m : ℝ) * (Fintype.card F : ℝ)) ^ (r + 1)) :=
  sup_pureFace_of_iterConvEnergyWick_le_q
    (F := F) (m := m) (lam := lam) (G := G)
    hfam hgrp J (le_trans hC0 hCC) hqq
    (iterConvEnergyWick_succ_of_prev_of_budget_le_const
      J q r hJ hC0 hCC hprev hbudget)
    hs

end ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters.iterConvEnergyWick_succ_of_prev_of_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters.iterConvEnergyWick_succ_of_prev_of_budget_le_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters.sup_pureFace_succ_of_iterConvEnergyWick_prev_of_budget_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R94IterConvSuccPublicConstantAdapters.sup_pureFace_succ_of_iterConvEnergyWick_prev_of_budget_le_const_q
