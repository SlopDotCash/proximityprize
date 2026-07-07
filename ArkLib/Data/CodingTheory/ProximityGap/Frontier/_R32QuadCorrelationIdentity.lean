/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30LagCorrelationIdentity

/-!
# LANE B2 (#466 round 32): four-λ orthogonality for the four-`J` correlation

The full four-`J` correlation identity needed by the `r = 3` decomposition expands four Jacobi
coefficients and then collapses the remaining `j`-sum by quotient-character orthogonality.

This brick lands that fixed-variable collapse:

`∑_j λ_{j+t₁}(x₁) λ_{j+t₂}(x₂) conj(λ_{j+s₁}(y₁)) conj(λ_j(y₂))`
equals
`m · 1_G(x₁ x₂ (y₁ y₂)⁻¹) · λ_{t₁}(x₁) λ_{t₂}(x₂) conj(λ_{s₁}(y₁))`
when `y₁,y₂ ≠ 0`, and packages the zero-row cleanup needed for the four-`J` integrand.

It is the exact orthogonality core of the pending four-`J` complete-sum identity. No analytic
input is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R32QuadCorrelationIdentity

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- The scalar part of the four-`J` expansion at fixed variables. -/
noncomputable def quadJacobiWeight (χ : F → ℂ) (x₁ x₂ y₁ y₂ : F) : ℂ :=
  χ (1 - x₁) * χ (1 - x₂) * (starRingEnd ℂ) (χ (1 - y₁))
    * (starRingEnd ℂ) (χ (1 - y₂))

/-- **Four-λ fixed-variable collapse.** This is the orthogonality engine behind the
balanced four-`J` correlation: after extracting the three visible lags, the remaining
`j`-sum is the quotient-dual indicator of `G`. -/
theorem quad_lambda_sum_identity
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (t₁ t₂ s₁ : ZMod m) (x₁ x₂ : F) {y₁ y₂ : F} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ∑ j : ZMod m,
        lam (j + t₁) x₁ * lam (j + t₂) x₂
          * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)
      = (m : ℂ) * ((if x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then (1 : ℂ) else 0)
          * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))) := by
  classical
  have hpt : ∀ j : ZMod m,
      lam (j + t₁) x₁ * lam (j + t₂) x₂
          * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)
        = (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))
            * lam j (x₁ * x₂ * (y₁ * y₂)⁻¹) := by
    intro j
    have hc₁ : (starRingEnd ℂ) (lam (j + s₁) y₁)
        = (starRingEnd ℂ) (lam s₁ y₁) * lam j y₁⁻¹ := by
      rw [hgrp.add_eq_mul j s₁ y₁, map_mul, ← lam_inv_eq_conj hfam hgrp j hy₁]
      ring
    have hc₂ : (starRingEnd ℂ) (lam j y₂) = lam j y₂⁻¹ :=
      (lam_inv_eq_conj hfam hgrp j hy₂).symm
    rw [hgrp.add_eq_mul j t₁ x₁, hgrp.add_eq_mul j t₂ x₂, hc₁, hc₂]
    have hw : lam j x₁ * lam j x₂ * lam j y₁⁻¹ * lam j y₂⁻¹
        = lam j (x₁ * x₂ * (y₁ * y₂)⁻¹) := by
      rw [← hfam.map_mul j x₁ x₂, ← hfam.map_mul j (x₁ * x₂) y₁⁻¹,
        ← hfam.map_mul j (x₁ * x₂ * y₁⁻¹) y₂⁻¹]
      congr 1
      rw [mul_inv]
      ring
    calc lam j x₁ * lam t₁ x₁ * (lam j x₂ * lam t₂ x₂)
          * ((starRingEnd ℂ) (lam s₁ y₁) * lam j y₁⁻¹) * lam j y₂⁻¹
        = (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))
            * (lam j x₁ * lam j x₂ * lam j y₁⁻¹ * lam j y₂⁻¹) := by ring
      _ = (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))
            * lam j (x₁ * x₂ * (y₁ * y₂)⁻¹) := by rw [hw]
  calc ∑ j : ZMod m,
        lam (j + t₁) x₁ * lam (j + t₂) x₂
          * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)
      = (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))
          * ∑ j : ZMod m, lam j (x₁ * x₂ * (y₁ * y₂)⁻¹) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => hpt j)
    _ = (m : ℂ) * ((if x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then (1 : ℂ) else 0)
          * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))) := by
        rw [hfam.indicator (x₁ * x₂ * (y₁ * y₂)⁻¹)]
        by_cases hmem : x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G
        · rw [if_pos hmem]
          ring
        · rw [if_neg hmem]
          ring

/-- **Fixed-variable four-`J` integrand collapse.** After expanding the four Jacobi
coefficients, the inner `j`-sum at fixed `x₁,x₂,y₁,y₂` is exactly the four-λ indicator
collapse multiplied by the scalar character weight, with the `y₁ = 0` or `y₂ = 0` rows
vanishing on both sides. -/
theorem quad_jacobi_integrand_sum_identity
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) (χ : F → ℂ)
    (t₁ t₂ s₁ : ZMod m) (x₁ x₂ y₁ y₂ : F) :
    ∑ j : ZMod m,
        quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam (j + t₁) x₁ * lam (j + t₂) x₂
            * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂))
      = (m : ℂ) * ((if y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then (1 : ℂ) else 0)
          * quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))) := by
  classical
  by_cases hy₁ : y₁ = 0
  · have hL : ∑ j : ZMod m,
        quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam (j + t₁) x₁ * lam (j + t₂) x₂
            * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hy₁, hfam.map_zero (j + s₁)]
      simp
    rw [hL, if_neg (by tauto)]
    ring
  by_cases hy₂ : y₂ = 0
  · have hL : ∑ j : ZMod m,
        quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam (j + t₁) x₁ * lam (j + t₂) x₂
            * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hy₂, hfam.map_zero j]
      simp
    rw [hL, if_neg (by tauto)]
    ring
  calc ∑ j : ZMod m,
        quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam (j + t₁) x₁ * lam (j + t₂) x₂
            * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂))
      = quadJacobiWeight χ x₁ x₂ y₁ y₂
          * ∑ j : ZMod m,
              lam (j + t₁) x₁ * lam (j + t₂) x₂
                * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂) := by
        rw [Finset.mul_sum]
    _ = quadJacobiWeight χ x₁ x₂ y₁ y₂
          * ((m : ℂ) * ((if x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then (1 : ℂ) else 0)
              * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁)))) := by
        rw [quad_lambda_sum_identity hfam hgrp t₁ t₂ s₁ x₁ x₂ hy₁ hy₂]
    _ = (m : ℂ) * ((if y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then (1 : ℂ) else 0)
          * quadJacobiWeight χ x₁ x₂ y₁ y₂
          * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))) := by
        by_cases hmem : x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G
        · rw [if_pos hmem, if_pos ⟨hy₁, hy₂, hmem⟩]
          ring
        · rw [if_neg hmem, if_neg (by tauto)]
          ring

end ArkLib.ProximityGap.Frontier.R32QuadCorrelationIdentity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R32QuadCorrelationIdentity.quad_lambda_sum_identity
#print axioms
  ArkLib.ProximityGap.Frontier.R32QuadCorrelationIdentity.quad_jacobi_integrand_sum_identity
