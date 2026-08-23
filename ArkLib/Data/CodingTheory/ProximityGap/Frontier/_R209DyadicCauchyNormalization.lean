/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R209 dyadic Cauchy normalization)
-/
import Mathlib.Tactic

/-!
# R209 (#466): dyadic Cauchy normalization

The concrete Gauss-period dilation recursion gives a triangle inequality
`‖parent‖ ≤ ‖left‖ + ‖right‖`.  The squared normalized spectrum used by the
MGF route has a doubled parent variance, so the deterministic pointwise input
needed by R188/R207 is the elementary Cauchy inequality

```text
((u + v)^2) / (2 σ²) ≤ u^2 / σ² + v^2 / σ².
```

This file isolates that normalization arithmetic.  It is deliberately pure
real analysis; no finite-field content is hidden here.
-/

namespace ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization

open Real

noncomputable section

/-- Scalar dyadic Cauchy normalization.  This is the variance-normalized form
of `(u + v)^2 ≤ 2(u^2 + v^2)`. -/
theorem half_sq_sum_div_le_sq_div_add_sq_div {u v σ : ℝ}
    (hσ : 0 < σ) :
    ((u + v) ^ 2) / (2 * σ ^ 2) ≤ u ^ 2 / σ ^ 2 + v ^ 2 / σ ^ 2 := by
  have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
  have hmain : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by nlinarith
  have hden : 0 < 2 * σ ^ 2 := by positivity
  calc
    ((u + v) ^ 2) / (2 * σ ^ 2)
        ≤ (2 * (u ^ 2 + v ^ 2)) / (2 * σ ^ 2) :=
          div_le_div_of_nonneg_right hmain hden.le
    _ = (u ^ 2 + v ^ 2) / σ ^ 2 := by field_simp [ne_of_gt hσ]
    _ = u ^ 2 / σ ^ 2 + v ^ 2 / σ ^ 2 := by ring

/-- If a raw parent magnitude is bounded by the sum of two child magnitudes,
then the doubled-variance normalized square is bounded by the sum of the two
child normalized squares. -/
theorem normalized_parent_sq_le_child_sq_sum {parent left right σ : ℝ}
    (hσ : 0 < σ)
    (hparent_nonneg : 0 ≤ parent)
    (hbound : parent ≤ left + right) :
    parent ^ 2 / (2 * σ ^ 2) ≤ left ^ 2 / σ ^ 2 + right ^ 2 / σ ^ 2 := by
  have hsum_nonneg : 0 ≤ left + right := le_trans hparent_nonneg hbound
  have hsquare : parent ^ 2 ≤ (left + right) ^ 2 :=
    by nlinarith
  have hden : 0 < 2 * σ ^ 2 := by positivity
  calc
    parent ^ 2 / (2 * σ ^ 2)
        ≤ (left + right) ^ 2 / (2 * σ ^ 2) :=
          div_le_div_of_nonneg_right hsquare hden.le
    _ ≤ left ^ 2 / σ ^ 2 + right ^ 2 / σ ^ 2 :=
      half_sq_sum_div_le_sq_div_add_sq_div hσ

/-- Pointwise finite-family version consumed by R207/R208-style abstract
spectra. -/
theorem normalized_parent_sq_le_child_sq_sum_on {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ) {σ : ℝ}
    (hσ : 0 < σ)
    (hparent_nonneg : ∀ i ∈ s, 0 ≤ parent i)
    (hbound : ∀ i ∈ s, parent i ≤ left i + right i) :
    ∀ i ∈ s,
      parent i ^ 2 / (2 * σ ^ 2) ≤
        left i ^ 2 / σ ^ 2 + right i ^ 2 / σ ^ 2 := by
  intro i hi
  exact normalized_parent_sq_le_child_sq_sum hσ (hparent_nonneg i hi) (hbound i hi)

end

end ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization

/-! ## Axiom audit -/
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization.half_sq_sum_div_le_sq_div_add_sq_div
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization.normalized_parent_sq_le_child_sq_sum
set_option linter.style.longLine false in
#print axioms ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization.normalized_parent_sq_le_child_sq_sum_on
