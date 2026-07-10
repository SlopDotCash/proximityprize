/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum

/-!
# The norm of a Gauss sum over a finite field

Mathlib proves `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card F`
(`gaussSum_mul_gaussSum_eq_card`) and `star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹`
(`star_gaussSum_eq`), but not the resulting classical magnitude statement
`‖gaussSum χ ψ‖ = √#F`.  This file supplies it (over `ℂ`, where `star_gaussSum_eq`
lives; a general `RCLike` target would need a `star_gaussSum_eq` generalization first).

## Main results

* `norm_gaussSum_sq_eq_card` : `‖gaussSum χ ψ‖ ^ 2 = Fintype.card F` for `χ` nontrivial and
  `ψ` primitive.
* `norm_gaussSum_eq_sqrt_card` : `‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F)`.

## Mathlib upstreaming target

`Mathlib/NumberTheory/GaussSum.lean`, section `GaussSumProd` (right after
`gaussSum_ne_zero_of_nontrivial`).  This is PR-2 of the #466 r24 upstream plan.
-/

variable {F : Type*} [Field F] [Fintype F]

/-- The squared norm of the Gauss sum of a nontrivial multiplicative character `χ : MulChar F ℂ`
and a primitive additive character `ψ` on a finite field `F` is the cardinality of `F`. -/
theorem norm_gaussSum_sq_eq_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h : gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ) = (Fintype.card F : ℂ) := by
    rw [starRingEnd_apply, star_gaussSum_eq]
    exact gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [Complex.mul_conj'] at h
  exact_mod_cast h

/-- **The Gauss-sum magnitude.** For a nontrivial multiplicative character `χ : MulChar F ℂ` and
a primitive additive character `ψ` on a finite field `F`,
`‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F)`. -/
theorem norm_gaussSum_eq_sqrt_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  rw [← norm_gaussSum_sq_eq_card hχ hψ, Real.sqrt_sq (norm_nonneg _)]
