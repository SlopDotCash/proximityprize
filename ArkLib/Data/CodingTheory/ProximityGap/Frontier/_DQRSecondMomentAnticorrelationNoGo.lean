/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# DQR: second-moment anticorrelation does not force depth-seven contraction

At one dyadic subgroup step, fine-scale period values occur in sibling pairs `(x_i,y_i)` and the
coarse period is `x_i+y_i` on both children.  The exact production-facing recursion has negative
aggregate sibling correlation.  This file records a falsify-first warning: zero means, equal
second moments, and even strictly negative sibling correlation do not by themselves imply the
Gaussian fourteenth-moment contraction factor `2^7`.

The four-pair rational array below consists of two aligned pairs and two slightly larger
anti-aligned pairs.  The anti-aligned pairs make the total correlation negative but vanish after
coarsening; the aligned pairs dominate the fourteenth moment.  Any proof of DQR-4 must therefore
use higher mixed moments or field-specific structure, not only the exact quadratic ledger.

Issue #466.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo

/-- Fine-scale values in the first child of each dyadic pair. -/
noncomputable def left : Fin 4 → ℝ := ![1, -1, 11 / 10, -(11 / 10)]

/-- Fine-scale values in the second child.  The first two pairs align and the last two oppose. -/
noncomputable def right : Fin 4 → ℝ := ![1, -1, -(11 / 10), 11 / 10]

/-- Each child array has exact mean zero. -/
theorem left_sum_eq_zero : ∑ i, left i = 0 := by
  norm_num [left, Fin.sum_univ_succ]

theorem right_sum_eq_zero : ∑ i, right i = 0 := by
  norm_num [right, Fin.sum_univ_succ]

/-- The two child arrays have identical quadratic energy. -/
theorem secondMoments_eq : ∑ i, left i ^ 2 = ∑ i, right i ^ 2 := by
  norm_num [left, right, Fin.sum_univ_succ]

/-- The aggregate sibling correlation is strictly negative. -/
theorem siblingCorrelation_lt_zero : ∑ i, left i * right i < 0 := by
  norm_num [left, right, Fin.sum_univ_succ]

/-- Despite all quadratic diagnostics above, duplicating the coarse value `x_i+y_i` on both
children expands the fourteenth moment by much more than the Gaussian factor `2^7`. -/
theorem fourteenthMoment_not_gaussianContractive :
    2 * (∑ i, (left i + right i) ^ 14) >
      2 ^ 7 * (∑ i, (left i ^ 14 + right i ^ 14)) := by
  norm_num [left, right, Fin.sum_univ_succ]

end ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo.left_sum_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo.right_sum_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo.secondMoments_eq
#print axioms
  ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo.siblingCorrelation_lt_zero
#print axioms
  ArkLib.ProximityGap.Frontier.DQRSecondMomentAnticorrelationNoGo.fourteenthMoment_not_gaussianContractive
