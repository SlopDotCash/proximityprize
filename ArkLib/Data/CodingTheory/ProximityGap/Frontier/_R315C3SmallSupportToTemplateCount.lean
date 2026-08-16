/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Ring

/-!
# R315 (#466): small c=3 support-pattern count ⇒ template count

R315 isolates the small `(6,3)` c=3 relation-web family.  The empirical support
law says that, for `n = 2m`, the small class has `3m - 9` support patterns:
three boundary supports lift to two signed templates each, while all remaining
supports lift to four signed templates each.

This file proves the arithmetic consumer:

`4 * ((3m - 9) - 3) + 2 * 3 = 6(n - 7)`.

The hard missing theorem is the actual support-pattern classification and the
two-vs-four lift count.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R315C3SmallSupportToTemplateCount

/-- The R315 small-family support/lift law gives `6(n-7)` signed templates. -/
theorem smallTemplateCount_of_supportLaw (m n supportCount boundaryCount : ℤ)
    (hn : n = 2 * m)
    (hSupport : supportCount = 3 * m - 9)
    (hBoundary : boundaryCount = 3) :
    4 * (supportCount - boundaryCount) + 2 * boundaryCount = 6 * (n - 7) := by
  subst n
  subst supportCount
  subst boundaryCount
  ring

/-- Equivalent form with `m = n/2` already eliminated. -/
theorem smallTemplateCount_evenForm (m : ℤ) :
    4 * ((3 * m - 9) - 3) + 2 * 3 = 6 * ((2 * m) - 7) := by
  ring

end ArkLib.ProximityGap.Frontier.R315C3SmallSupportToTemplateCount

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R315C3SmallSupportToTemplateCount.smallTemplateCount_of_supportLaw
#print axioms ArkLib.ProximityGap.Frontier.R315C3SmallSupportToTemplateCount.smallTemplateCount_evenForm
