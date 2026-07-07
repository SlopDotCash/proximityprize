/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R26PointwiseTripleConvTarget

/-!
# LANE B2 (#466 round 88): stable constant adapters for the r = 3 triple-convolution core

The calibrated open core `TripleConvEnergyBound J q C` and its pointwise/Hermitian refinements are
monotone in the constant.  R26 already contains Jacobi-specialized `*_le` consumers; this file
records the generic adapters for the stable exported pointwise surface, so future Katz/Hasse
estimates can land at a sharp internal constant and publish at a larger campaign constant without
redoing arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput
open ArkLib.ProximityGap.Frontier.R26PointwiseTripleConvTarget

variable {m : ℕ} [NeZero m]

/-- `TripleConvEnergyBound` is monotone in its real constant. -/
theorem tripleConvEnergyBound_mono_const
    (J : ZMod m → ℂ) (q : ℕ) {C C' : ℝ}
    (hCC : C ≤ C') (h : TripleConvEnergyBound J q C) :
    TripleConvEnergyBound J q C' := by
  unfold TripleConvEnergyBound at *
  have hm : 0 ≤ (m : ℝ) ^ 3 := by positivity
  have hq : 0 ≤ (q : ℝ) ^ 3 := by positivity
  have hC_m : C * (m : ℝ) ^ 3 ≤ C' * (m : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_right hCC hm
  exact h.trans (mul_le_mul_of_nonneg_right hC_m hq)

/-- The triple-convolution pointwise target is monotone in its constant. -/
theorem tripleConvPointwiseBound_mono_const
    (J : ZMod m → ℂ) (q : ℕ) {C C' : ℝ}
    (hCC : C ≤ C') (h : TripleConvPointwiseBound J q C) :
    TripleConvPointwiseBound J q C' := by
  intro d
  have hm : 0 ≤ (m : ℝ) ^ 2 := by positivity
  have hq : 0 ≤ (q : ℝ) ^ 3 := by positivity
  have hC_m : C * (m : ℝ) ^ 2 ≤ C' * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hCC hm
  exact (h d).trans (mul_le_mul_of_nonneg_right hC_m hq)

/-- A sharp generic pointwise certificate can be consumed as the R23 energy input at any larger
published constant. -/
theorem tripleConvEnergyBound_of_pointwise_le
    (J : ZMod m → ℂ) (q : ℕ) {C C' : ℝ}
    (hCC : C ≤ C') (hpt : TripleConvPointwiseBound J q C) :
    TripleConvEnergyBound J q C' :=
  tripleConvEnergyBound_of_pointwise J q
    (tripleConvPointwiseBound_mono_const J q hCC hpt)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- Generic energy monotonicity transported to the Jacobi coefficient sequence. -/
theorem jacobiTripleConvEnergyBound_mono_const
    {C C' : ℝ} (hCC : C ≤ C')
    (h : TripleConvEnergyBound
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) C) :
    TripleConvEnergyBound
      (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) C' :=
  tripleConvEnergyBound_mono_const
    (fun i : ZMod m => jacobiCoeff χ lam i) (Fintype.card F) hCC h

end ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters.tripleConvEnergyBound_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters.tripleConvPointwiseBound_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R88TripleConvConstantAdapters.tripleConvEnergyBound_of_pointwise_le
