/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R216 Gauss-period one-child normalized-square MGF)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R213NonzeroNormalizedSqQuarterMGFResidualConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R215OneChildDirectMGFLaw

/-!
# R216 (#466): actual Gauss-period normalized-square child permutation

R215 says that the raw dyadic prize step only needs one direct child MGF law
when the right child normalized-square spectrum is a permutation of the left.
For the concrete Gauss-period dilation split, that permutation is multiplication
by the nonzero dilation scalar on frequency space.

This file packages the deterministic part:

* multiplication by `ζ ≠ 0` is a permutation preserving `nonzeroFreqs`;
* the normalized-square right child
  `b ↦ ‖η_G(ζ * b)‖² / σ²`
  is therefore a permuted copy of the left child
  `b ↦ ‖η_G(b)‖² / σ²`;
* R213's concrete nonzero normalized-square residual supplies the one direct
  child law used by R215.

The analytic content remains exactly R213's one-child quarter-MGF residual.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R216GaussPeriodOneChildNormalizedSqMGF

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw
open ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Multiplication by a nonzero field element as a permutation of frequency
space. -/
noncomputable def mulLeftPerm (ζ : F) (hζ : ζ ≠ 0) : Equiv.Perm F where
  toFun b := ζ * b
  invFun b := ζ⁻¹ * b
  left_inv b := by
    simp [hζ]
  right_inv b := by
    simp [hζ]

/-- The multiplicative-frequency permutation preserves nonzero frequencies. -/
theorem mulLeftPerm_mem_nonzeroFreqs {ζ : F} (hζ : ζ ≠ 0) (b : F) :
    mulLeftPerm ζ hζ b ∈ nonzeroFreqs (F := F) ↔
      b ∈ nonzeroFreqs (F := F) := by
  rw [mem_nonzeroFreqs, mem_nonzeroFreqs]
  constructor
  · intro hb hzero
    apply hb
    simp [mulLeftPerm, hzero]
  · intro hb
    exact mul_ne_zero hζ hb

/-- R213's normalized-square residual is precisely the direct one-child MGF
law for the concrete nonzero Gauss-period child spectrum. -/
theorem largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ) :
    LargeIndexChildQuarterMGFLaw (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖) σ := by
  exact hMGF

/-- The shifted concrete child inherits the direct child-MGF law from the
unshifted one by the nonzero multiplicative frequency permutation. -/
theorem largeIndexChildQuarterMGF_shift_of_nonzeroNormalizedSqResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0)
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ) :
    LargeIndexChildQuarterMGFLaw (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G (ζ * b)‖) σ := by
  refine largeIndexChildQuarterMGF_of_perm
    (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖)
    σ (mulLeftPerm ζ hζ) ?_ ?_
    (largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual ψ G hMGF)
  · intro b
    exact mulLeftPerm_mem_nonzeroFreqs hζ b
  · intro b _
    rfl

end ArkLib.ProximityGap.Frontier.R216GaussPeriodOneChildNormalizedSqMGF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R216GaussPeriodOneChildNormalizedSqMGF.mulLeftPerm_mem_nonzeroFreqs
#print axioms ArkLib.ProximityGap.Frontier.R216GaussPeriodOneChildNormalizedSqMGF.largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual
#print axioms ArkLib.ProximityGap.Frontier.R216GaussPeriodOneChildNormalizedSqMGF.largeIndexChildQuarterMGF_shift_of_nonzeroNormalizedSqResidual
