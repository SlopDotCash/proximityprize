/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# R316 (#466): three small-support families imply `3m - 9` supports

R316 refines R315's small `(6,3)` support-pattern count into three explicit
one-parameter families, each with `m - 3` admissible parameters.  This file is
the arithmetic consumer: if the H, K, and D families are disjoint and each has
cardinality `m - 3`, then their union has `3m - 9` support patterns.

The hard missing theorem remains the actual support-family classification and
disjointness under the signed relation `g^h = ±3`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R316C3SmallFamiliesToSupportCount

/-- Three disjoint one-parameter families of size `m - 3` have total size `3m - 9`. -/
theorem supportCount_of_threeFamilies
    (m hFamily kFamily dFamily supportCount : ℤ)
    (hH : hFamily = m - 3)
    (hK : kFamily = m - 3)
    (hD : dFamily = m - 3)
    (hSupport : supportCount = hFamily + kFamily + dFamily) :
    supportCount = 3 * m - 9 := by
  subst supportCount
  subst hFamily
  subst kFamily
  subst dFamily
  ring

/-- The R316 support count feeds the R315 signed-template count arithmetic. -/
theorem signedTemplateCount_of_threeFamilies (m : ℤ) :
    4 * (((m - 3) + (m - 3) + (m - 3)) - 3) + 2 * 3
      = 6 * ((2 * m) - 7) := by
  ring

end ArkLib.ProximityGap.Frontier.R316C3SmallFamiliesToSupportCount

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R316C3SmallFamiliesToSupportCount.supportCount_of_threeFamilies
#print axioms ArkLib.ProximityGap.Frontier.R316C3SmallFamiliesToSupportCount.signedTemplateCount_of_threeFamilies
