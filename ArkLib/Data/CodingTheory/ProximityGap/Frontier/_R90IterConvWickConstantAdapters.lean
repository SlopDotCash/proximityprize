/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FullTowerCollapse

/-!
# LANE B2 (#466 round 90): constant adapters for the deep iterated-convolution wall

The final ladder object `IterConvEnergyWick J q r C` uses `C ^ r`, so publishing a sharp
certificate at a larger public constant needs the usual nonnegativity side condition.  This file
records that adapter, plus the matching sup-consumer wrapper for the full-tower collapse.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R27FullTowerCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- `IterConvEnergyWick` is monotone in its real constant, provided the sharper constant is
nonnegative. -/
theorem iterConvEnergyWick_mono_const
    (J : ZMod m → ℂ) (q r : ℕ) {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (h : IterConvEnergyWick J q r C) :
    IterConvEnergyWick J q r C' := by
  unfold IterConvEnergyWick at *
  have hpow : C ^ r ≤ C' ^ r := pow_le_pow_left₀ hC0 hCC r
  have hfac : 0 ≤ (r.factorial : ℝ) := by positivity
  have hmq : 0 ≤ ((m : ℝ) * (q : ℝ)) ^ r := by positivity
  have hpow_fac : C ^ r * (r.factorial : ℝ) ≤ C' ^ r * (r.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right hpow hfac
  exact h.trans (mul_le_mul_of_nonneg_right hpow_fac hmq)

/-- `IterConvEnergyWick` is monotone in the ambient size parameter `q`, provided the Wick
constant is nonnegative. -/
theorem iterConvEnergyWick_mono_q
    (J : ZMod m → ℂ) {q q' r : ℕ} {C : ℝ}
    (hC0 : 0 ≤ C) (hqq : q ≤ q')
    (h : IterConvEnergyWick J q r C) :
    IterConvEnergyWick J q' r C := by
  unfold IterConvEnergyWick at *
  have hmq : (m : ℝ) * (q : ℝ) ≤ (m : ℝ) * (q' : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqq) (by positivity)
  have hmqpow : ((m : ℝ) * (q : ℝ)) ^ r ≤ ((m : ℝ) * (q' : ℝ)) ^ r :=
    pow_le_pow_left₀ (by positivity) hmq r
  have hcoef : 0 ≤ C ^ r * (r.factorial : ℝ) := by positivity
  exact h.trans (mul_le_mul_of_nonneg_left hmqpow hcoef)

/-- Combined monotonicity in both the public Wick constant and ambient size parameter. -/
theorem iterConvEnergyWick_mono_const_q
    (J : ZMod m → ℂ) {q q' r : ℕ} {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ q')
    (h : IterConvEnergyWick J q r C) :
    IterConvEnergyWick J q' r C' :=
  iterConvEnergyWick_mono_const J q' r hC0 hCC
    (iterConvEnergyWick_mono_q J hC0 hqq h)

/-- A sharp deep-rung certificate can be consumed by the full-tower sup bound at any larger
published Wick constant. -/
theorem sup_pureFace_of_iterConvEnergyWick_le_const
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {r : ℕ} {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C')
    (h : IterConvEnergyWick J (Fintype.card F) r C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * r)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ r * (r.factorial : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ r) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_mono_const J (Fintype.card F) r hC0 hCC h) hs

/-- A deep-rung certificate at a smaller ambient size can be consumed by the full-tower sup bound
at the actual field size. -/
theorem sup_pureFace_of_iterConvEnergyWick_le_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q r : ℕ} {C : ℝ}
    (hC0 : 0 ≤ C) (hqq : q ≤ Fintype.card F)
    (h : IterConvEnergyWick J q r C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * r)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C ^ r * (r.factorial : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ r) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_mono_q J hC0 hqq h) hs

/-- A deep-rung certificate at a smaller ambient size and sharper constant can be consumed by the
full-tower sup bound at the actual field size and larger public constant. -/
theorem sup_pureFace_of_iterConvEnergyWick_le_const_q
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (J : ZMod m → ℂ) {q r : ℕ} {C C' : ℝ}
    (hC0 : 0 ≤ C) (hCC : C ≤ C') (hqq : q ≤ Fintype.card F)
    (h : IterConvEnergyWick J q r C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ (2 * r)
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ)
          * (C' ^ r * (r.factorial : ℝ) * ((m : ℝ) * (Fintype.card F : ℝ)) ^ r) :=
  sup_pureFace_of_iterConvEnergyWick hfam hgrp J
    (iterConvEnergyWick_mono_const_q J hC0 hCC hqq h) hs

end ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.iterConvEnergyWick_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.iterConvEnergyWick_mono_q
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.iterConvEnergyWick_mono_const_q
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.sup_pureFace_of_iterConvEnergyWick_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.sup_pureFace_of_iterConvEnergyWick_le_q
#print axioms
  ArkLib.ProximityGap.Frontier.R90IterConvWickConstantAdapters.sup_pureFace_of_iterConvEnergyWick_le_const_q
