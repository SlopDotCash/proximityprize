/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._P1RateQuarterCommonFactorConstruction

/-!
# Compatibility names for the concrete P1 common locator

The structural construction now proves the locator interface through generic finite-product
lemmas. Reuse that implementation and its evaluation theorems; the original direct large-finite
product attempt had the same polynomial but duplicated the public evaluation and residual names.
-/

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction

/-- Compatibility name for the common-root product supplied by the structural construction. -/
noncomputable abbrev concreteCommonLocator : F[X] := concreteCommonLocatorPolynomial

/-- The original degree bound, supplied by the owner's exact degree formula. -/
theorem concreteCommonLocator_natDegree_le : concreteCommonLocator.natDegree ≤ 2 * d :=
  concreteCommonLocator_natDegree.le

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction

#print axioms ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction.concreteCommonLocator_natDegree_le
