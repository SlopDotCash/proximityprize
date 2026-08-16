/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Gaussian supremum approximation has an additive-error slack gate

High-dimensional Gaussian approximation theorems for suprema, such as CCK-style comparison and
anti-concentration results, are a natural-looking way to import an extreme-value heuristic into
issue #464.  This file records the finite last-mile obstruction that such a route must still pass.

An additive comparison

`actualSup <= gaussianSup + error`

proves the target `actualSup <= target` only if the Gaussian supremum theorem lands below
`target - error`.  Equivalently, in normalized constants, a Gaussian constant `Cg` and coupling
constant `Ce` fit under the target constant `Ct` exactly when `Cg + Ce <= Ct`.  A sharp Gaussian
constant has no room for any positive coupling error.

The file is deliberately abstract.  It does not assert independence, randomness, or a Gaussian
approximation for Gauss periods.  It only fixes the bookkeeping any proposed Gaussian-supremum
transfer must satisfy before it can imply the dyadic-subgroup proximity-gap floor.
-/

namespace ArkLib.ProximityGap.Frontier.GaussianSupCouplingErrorGate

/-- A one-sided additive comparison between an actual supremum and a Gaussian surrogate. -/
def CouplingUpper (actual gaussian error : ℝ) : Prop :=
  actual <= gaussian + error

/-- The additive comparison reaches a target exactly when the Gaussian side has target-minus-error
slack. -/
theorem gaussian_plus_error_le_target_iff {gaussian error target : ℝ} :
    gaussian + error <= target ↔ gaussian <= target - error := by
  constructor <;> intro h <;> linarith

/-- Consumer form: a Gaussian bound below `target - error` turns an additive coupling into the
actual target bound. -/
theorem actual_le_target_of_gaussian_slack
    {actual gaussian error target : ℝ}
    (hc : CouplingUpper actual gaussian error)
    (hg : gaussian <= target - error) :
    actual <= target := by
  unfold CouplingUpper at hc
  linarith

/-- Sharp Gaussian control leaves no room for a positive additive comparison error. -/
theorem sharp_gaussian_with_positive_error_exceeds_target
    {gaussian error target : ℝ}
    (hsharp : gaussian = target)
    (herror : 0 < error) :
    target < gaussian + error := by
  rw [hsharp]
  linarith

/-- A normalized supremum bound with an explicit constant and scale. -/
def NormalizedSupBound (const scale value : ℝ) : Prop :=
  value <= const * scale

/-- Normalized consumer: if the Gaussian surrogate costs `Cg * scale` and the additive comparison
costs `Ce * scale`, then the actual bound reaches the target constant exactly through the budget
`Cg + Ce <= Ct`. -/
theorem normalized_coupling_constant_consumer
    {actual gaussian scale Cg Ce Ct : ℝ}
    (hscale : 0 <= scale)
    (hg : NormalizedSupBound Cg scale gaussian)
    (hc : actual <= gaussian + Ce * scale)
    (hbudget : Cg + Ce <= Ct) :
    actual <= Ct * scale := by
  unfold NormalizedSupBound at hg
  have hsum : gaussian + Ce * scale <= Cg * scale + Ce * scale := by
    simpa [add_comm] using add_le_add_right hg (Ce * scale)
  have hbudget_scaled : (Cg + Ce) * scale <= Ct * scale :=
    mul_le_mul_of_nonneg_right hbudget hscale
  calc
    actual <= gaussian + Ce * scale := hc
    _ <= Cg * scale + Ce * scale := hsum
    _ = (Cg + Ce) * scale := by ring
    _ <= Ct * scale := hbudget_scaled

/-- The constant budget is exactly the statement that the coupling error fits in the slack between
the target constant and the Gaussian constant. -/
theorem normalized_constant_budget_iff_error_slack {Cg Ce Ct : ℝ} :
    Cg + Ce <= Ct ↔ Ce <= Ct - Cg := by
  constructor <;> intro h <;> linarith

/-- A sharp Gaussian constant cannot absorb any positive normalized coupling error. -/
theorem sharp_gaussian_constant_allows_no_positive_error
    {Cg Ce : ℝ}
    (hCe : 0 < Ce) :
    ¬ Cg + Ce <= Cg := by
  intro h
  linarith

/-- At positive scale, a positive coupling constant strictly raises the normalized bound. -/
theorem normalized_sharp_bound_misses_with_positive_error
    {scale Cg Ce : ℝ}
    (hscale : 0 < scale)
    (hCe : 0 < Ce) :
    Cg * scale < (Cg + Ce) * scale := by
  have hconst : Cg < Cg + Ce := by linarith
  exact mul_lt_mul_of_pos_right hconst hscale

/-! ## Axiom audit -/
#print axioms gaussian_plus_error_le_target_iff
#print axioms actual_le_target_of_gaussian_slack
#print axioms sharp_gaussian_with_positive_error_exceeds_target
#print axioms normalized_coupling_constant_consumer
#print axioms normalized_constant_budget_iff_error_slack
#print axioms sharp_gaussian_constant_allows_no_positive_error
#print axioms normalized_sharp_bound_misses_with_positive_error

end ArkLib.ProximityGap.Frontier.GaussianSupCouplingErrorGate
