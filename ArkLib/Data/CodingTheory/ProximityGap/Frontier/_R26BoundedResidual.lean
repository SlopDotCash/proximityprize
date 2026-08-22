/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17TchiMomentIdentities

/-!
# LANE RESL2 (#466 round 26): bounded-residual support lemmas

The original round-26 residual draft tried to prove a full cross-character L² residual
estimate in one step.  The target is still useful, but the first draft mixed several
independent ingredients: unit-circle character values, conjugation-as-inversion, distinct
character orthogonality, Jacobi-kernel reindexing, and fourth-moment bookkeeping.

This file lands the small reusable algebraic part, axiom-clean:

* `norm_mulChar_eq_one_of_ne_zero`
* `norm_mulChar_le_one`
* `conj_mulChar`
* `sum_mulChar_mul_conj_eq_zero`

These are the elementary facts needed before rebuilding the cross-kernel identity in a
separate, better factored lane.  No residual L² or prize-closure claim is made here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities

namespace ArkLib.ProximityGap.Frontier.R26BoundedResidual

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Unit-circle values: `‖χ(a)‖ = 1` for `a ≠ 0`. -/
theorem norm_mulChar_eq_one_of_ne_zero (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    ‖χ a‖ = 1 := by
  have hpow : χ a ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  have hcard : Fintype.card F - 1 ≠ 0 := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  exact Complex.norm_eq_one_of_pow_eq_one hpow hcard

/-- `‖χ(a)‖ ≤ 1` for every `a`. -/
theorem norm_mulChar_le_one (χ : MulChar F ℂ) (a : F) : ‖χ a‖ ≤ 1 := by
  by_cases ha : a = 0
  · subst ha
    rw [χ.map_nonunit (by simp)]
    simp
  · exact le_of_eq (norm_mulChar_eq_one_of_ne_zero χ ha)

/-- Complex conjugation of a multiplicative character value is the inverse character. -/
theorem conj_mulChar (χ : MulChar F ℂ) (a : F) : conj' (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv' χ a]
  by_cases ha : IsUnit a
  · have ha0 : a ≠ 0 := ha.ne_zero
    have h1 : χ a * conj' (χ a) = 1 := mulChar_mul_conj χ ha0
    exact eq_inv_of_mul_eq_one_right h1
  · rw [χ.map_nonunit ha]
    simp

/-- Distinct-character orthogonality:
`∑ a, χ'(a)·conj(χ''(a)) = 0` for `χ' ≠ χ''`. -/
theorem sum_mulChar_mul_conj_eq_zero {χ' χ'' : MulChar F ℂ} (hne : χ' ≠ χ'') :
    ∑ a : F, χ' a * conj' (χ'' a) = 0 := by
  have hterm : ∀ a : F, χ' a * conj' (χ'' a) = (χ' * χ''⁻¹) a := by
    intro a
    rw [conj_mulChar, MulChar.coeToFun_mul, Pi.mul_apply]
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  exact MulChar.sum_eq_zero_of_ne_one (by rwa [Ne, mul_inv_eq_one])

end ArkLib.ProximityGap.Frontier.R26BoundedResidual

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R26BoundedResidual

#print axioms norm_mulChar_eq_one_of_ne_zero
#print axioms norm_mulChar_le_one
#print axioms conj_mulChar
#print axioms sum_mulChar_mul_conj_eq_zero
