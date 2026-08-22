/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R190 dyadic tail split consumer)
-/
import Mathlib

/-!
# R190 (#466): deterministic dyadic tail split

R188/R189 corrected the naive "large parent forces both children large" idea.
The true pointwise statement is a two-channel split:

```text
parent ≤ left + right, parent ≥ T
  ⟹ max(left,right) ≥ aT  OR  both children ≥ (1-a)T.
```

The first branch is an inherited one-child spike; the second is a balanced
two-child merge.  This file proves only the deterministic algebraic split.
The open analytic content remains: control the inherited branch recursively and
the balanced branch by child-pair equidistribution/cancellation.
-/

namespace ArkLib.ProximityGap.Frontier.R190DyadicTailSplitConsumer

/-- **Dyadic two-channel tail split.**  If a parent score is bounded by the sum
of two child scores and is at least `T`, then either one child reaches the
large-child threshold `a*T`, or both children reach the complementary threshold
`(1-a)*T`.

No sign, probability, or Gauss-period structure is used here; it is the exact
deterministic hinge exposed by R189. -/
theorem parent_tail_split {parent left right T a : ℝ}
    (hparent : parent ≤ left + right)
    (htail : T ≤ parent) :
    a * T ≤ left ∨ a * T ≤ right ∨ (1 - a) * T ≤ left ∧ (1 - a) * T ≤ right := by
  by_cases hL : a * T ≤ left
  · exact Or.inl hL
  · by_cases hR : a * T ≤ right
    · exact Or.inr (Or.inl hR)
    · push_neg at hL hR
      have hsum : T ≤ left + right := htail.trans hparent
      have hleft : (1 - a) * T ≤ left := by nlinarith
      have hright : (1 - a) * T ≤ right := by nlinarith
      exact Or.inr (Or.inr ⟨hleft, hright⟩)

/-- Contrapositive form: if neither child reaches the large-child threshold and
one child misses the complementary threshold, then the parent misses `T`. -/
theorem parent_lt_of_not_split {parent left right T a : ℝ}
    (hparent : parent ≤ left + right)
    (hL : left < a * T)
    (hR : right < a * T)
    (hSmall : left < (1 - a) * T ∨ right < (1 - a) * T) :
    parent < T := by
  have hsum : left + right < T := by
    rcases hSmall with hsmall | hsmall
    · nlinarith
    · nlinarith
  exact lt_of_le_of_lt hparent hsum

end ArkLib.ProximityGap.Frontier.R190DyadicTailSplitConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R190DyadicTailSplitConsumer.parent_tail_split
#print axioms ArkLib.ProximityGap.Frontier.R190DyadicTailSplitConsumer.parent_lt_of_not_split
