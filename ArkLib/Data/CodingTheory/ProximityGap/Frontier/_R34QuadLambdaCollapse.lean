/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R30LagCorrelationIdentity

/-!
# LANE B2 (#466 round 34): balanced four-λ orthogonality collapse

The full four-`J` correlation identity expands into a fixed-variable orthogonality
calculation.  This brick isolates and proves that calculation:

`Σ_j λ_{j+t₁}(x₁) λ_{j+t₂}(x₂) conj(λ_{j+s₁}(y₁)) conj(λ_j(y₂))`
collapses, for `y₁,y₂ ≠ 0`, to the phase
`λ_{t₁}(x₁) λ_{t₂}(x₂) conj(λ_{s₁}(y₁))` times the subgroup indicator of
`x₁*x₂*(y₁*y₂)⁻¹`.

This is the exact algebraic core needed by the round-32 four-correlation collapse; the
remaining work there is finite-sum binder choreography, not new orthogonality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R34QuadLambdaCollapse

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **Balanced four-λ collapse.**  The `j`-sum of the balanced shifted product is the
subgroup indicator at `x₁*x₂*(y₁*y₂)⁻¹`, multiplied by the external lag phases. -/
theorem quadLambda_collapse (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (t₁ t₂ s₁ : ZMod m)
    (x₁ x₂ y₁ y₂ : F) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ∑ j : ZMod m, lam (j + t₁) x₁ * lam (j + t₂) x₂
        * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)
      = (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))
          * ((m : ℂ) * (if x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then 1 else 0)) := by
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
  rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.mul_sum,
    hfam.indicator (x₁ * x₂ * (y₁ * y₂)⁻¹)]

/-- The same collapse with the subgroup indicator moved to the front, matching the
four-correlation expansion's fixed-variable target shape. -/
theorem quadLambda_collapse_indicator_front (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (t₁ t₂ s₁ : ZMod m)
    (x₁ x₂ y₁ y₂ : F) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ∑ j : ZMod m, lam (j + t₁) x₁ * lam (j + t₂) x₂
        * (starRingEnd ℂ) (lam (j + s₁) y₁) * (starRingEnd ℂ) (lam j y₂)
      = (m : ℂ) * ((if x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G then 1 else 0)
          * (lam t₁ x₁ * lam t₂ x₂ * (starRingEnd ℂ) (lam s₁ y₁))) := by
  rw [quadLambda_collapse hfam hgrp t₁ t₂ s₁ x₁ x₂ y₁ y₂ hy₁ hy₂]
  by_cases hmem : x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ G
  · rw [if_pos hmem]
    ring
  · rw [if_neg hmem]
    ring

end ArkLib.ProximityGap.Frontier.R34QuadLambdaCollapse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R34QuadLambdaCollapse.quadLambda_collapse
#print axioms
  ArkLib.ProximityGap.Frontier.R34QuadLambdaCollapse.quadLambda_collapse_indicator_front
