/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Fixed-character Jacobi coboundary audit

For a nontrivial quadratic multiplicative character `χ`, the fixed-second-argument Jacobi
sequence has an exact antipodal product law away from its two degenerate indices:

`J(α, χ) * J(αχ, χ) = g(χ)^2 = χ(-1) * #F`.

The first equality is the length-two translation-coboundary telescope.  It is the precise
specialization of

`J(α, χ) = g(α) g(χ) / g(αχ)`

when translation by `χ` is an involution.  The second equality is the quadratic Gauss-sum
identity.  In particular, the product has magnitude `#F`, so Hasse--Davenport/Gauss-ratio
structure supplies phase coupling but no contraction of the Jacobi pair.

The hypotheses `α != 1` and `αχ != 1` remove exactly the exceptional orbit containing the
trivial character.  That orbit has unit-size Jacobi factors instead of square-root-size ones.
No convolution-energy bound is asserted here: the identity is an algebra brick for auditing
that possible route.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.JacobiFixedChiCoboundaryAudit

variable {F : Type*} [Field F] [Fintype F]

/-- **Quadratic fixed-character coboundary telescope.**  Away from the exceptional orbit,
translation by a quadratic character pairs two Jacobi sums whose product is the square of the
quadratic Gauss sum. -/
theorem jacobi_antipodal_product_eq_gauss_sq
    {α χ : MulChar F ℂ} (hα : α ≠ 1) (hχ : χ.IsQuadratic)
    (hαχ : α * χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    jacobiSum α χ * jacobiSum (α * χ) χ = gaussSum χ ψ ^ 2 := by
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩).ne'
  have hαχχ : (α * χ) * χ ≠ 1 := by
    simpa [mul_assoc, ← pow_two, hχ.sq_eq_one] using hα
  have hj₁ := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
    hcard hαχ hψ
  have hj₂ := jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
    hcard hαχχ hψ
  have hgα : gaussSum α ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hα hψ
  have hgαχ : gaussSum (α * χ) ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hαχ hψ
  rw [hj₁, hj₂]
  rw [show (α * χ) * χ = α by
    rw [mul_assoc, ← pow_two, hχ.sq_eq_one, mul_one]]
  field_simp

/-- The telescoped pair is exactly `χ(-1) * #F`; in particular its scale is `#F`, not a
power-saving scale. -/
theorem jacobi_antipodal_product_eq_char_card
    {α χ : MulChar F ℂ} (hα : α ≠ 1) (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    (hαχ : α * χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    jacobiSum α χ * jacobiSum (α * χ) χ = χ (-1) * Fintype.card F := by
  rw [jacobi_antipodal_product_eq_gauss_sq hα hχ₂ hαχ hψ]
  exact gaussSum_sq hχ₁ hχ₂ hψ

/-- **No modulus contraction.**  The norm of every generic quadratic antipodal Jacobi pair is
exactly the field cardinality. -/
theorem norm_jacobi_antipodal_product_eq_card
    {α χ : MulChar F ℂ} (hα : α ≠ 1) (hχ₁ : χ ≠ 1) (hχ₂ : χ.IsQuadratic)
    (hαχ : α * χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖jacobiSum α χ * jacobiSum (α * χ) χ‖ = Fintype.card F := by
  have hχneg : ‖χ (-1)‖ = 1 := by
    rcases hχ₂ (-1) with hzero | hone | hneg
    · have hsquare : χ (-1) * χ (-1) = 1 := by
        rw [← map_mul]
        norm_num
      rw [hzero, zero_mul] at hsquare
      exact (zero_ne_one hsquare).elim
    · simp [hone]
    · simp [hneg]
  rw [jacobi_antipodal_product_eq_char_card hα hχ₁ hχ₂ hαχ hψ,
    norm_mul, hχneg, one_mul, Complex.norm_natCast]

end ArkLib.ProximityGap.Frontier.JacobiFixedChiCoboundaryAudit

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.JacobiFixedChiCoboundaryAudit.jacobi_antipodal_product_eq_gauss_sq
#print axioms
  ArkLib.ProximityGap.Frontier.JacobiFixedChiCoboundaryAudit.jacobi_antipodal_product_eq_char_card
#print axioms
  ArkLib.ProximityGap.Frontier.JacobiFixedChiCoboundaryAudit.norm_jacobi_antipodal_product_eq_card
