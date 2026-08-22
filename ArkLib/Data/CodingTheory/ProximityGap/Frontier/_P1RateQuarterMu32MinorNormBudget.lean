/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30

/-!
# Prize-field budget for `mu_32` locator minors

This file checks the exact integer endpoint of the cyclotomic minor-norm
argument for disjoint degree-seven locators on `mu_32`.

For an anchor coefficient `e_1` or `e_6`, the difference vector has squared
`l2` norm at most `14`.  Every elementary-coefficient difference has `l1`
norm at most `2 * choose(7,3) = 70`.  Young's inequality therefore bounds the
minor's `l2` norm by `2*70*sqrt(14)`.  Parseval over all thirty-two characters
and AM--GM over the sixteen odd embeddings give the algebraic norm ceiling

`(2 * ((2*70)^2 * 14))^8 = 548800^8`.

The theorems below certify that this is strictly smaller than the concrete
prize prime `P`.  The analytic Parseval-to-norm transfer and the finite
`(e_1,e_6)` collision census live outside this arithmetic-only file.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterMu32MinorNormBudget

open ArkLib.ProximityGap.PrizeShapePrimeP30

/-- Squared `l2` budget for an anchored locator minor. -/
theorem anchoredMinor_l2Sq_budget : (2 * 70) ^ 2 * 14 = 274400 := by
  norm_num

/-- Parseval changes the full-character energy into this conjugate mean-square
budget. -/
theorem anchoredMinor_conjugateMeanSq_budget : 2 * 274400 = 548800 := by
  norm_num

/-- **The minor norm ceiling is smaller than the certified prize prime.** -/
theorem anchoredMinor_norm_lt_prizePrime :
    548800 ^ 8 < P := by
  norm_num [P]

/-- The exact norm ceiling, useful when auditing external certificates. -/
theorem anchoredMinor_normCeiling_value :
    548800 ^ 8 = 8228351233069416798082784296960000000000000000 := by
  norm_num

end ArkLib.ProximityGap.Frontier.P1RateQuarterMu32MinorNormBudget

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterMu32MinorNormBudget
#print axioms anchoredMinor_l2Sq_budget
#print axioms anchoredMinor_conjugateMeanSq_budget
#print axioms anchoredMinor_norm_lt_prizePrime
#print axioms anchoredMinor_normCeiling_value
