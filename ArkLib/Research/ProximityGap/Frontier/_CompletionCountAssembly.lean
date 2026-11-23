/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._CompletionCountThirdMoment
import ArkLib.Research.ProximityGap.Frontier._ThirdMomentCap

/-!
# The completion count from the line structure alone

`_CompletionCountThirdMoment` bounds the surviving completions of a pair from
two inputs: a mass bound and a third-moment cap. `_ThirdMomentCap` derives that
cap from a line structure. This module composes them, so the completion count
follows from the line structure and the mass bound with no assumed moment
input left.

The composed statement is `completion_count_from_lines`. Specialising to the
first sponsor cutoff gives `first_sponsor_completion_from_lines`: with
`L = 311815756` coordinates, agreement cap `k = 159450661`, error allowance
`u = 62061713` and the eleven-head line cap, at most `4806` heads survive.

What is still external to this chain is the construction of the locator heads
and the concrete agreement cap they admit, both written arguments in the
draft. This module closes the counting interface, not the geometry.
-/

set_option autoImplicit false

namespace ProximityGap.CompletionCountAssembly

open scoped BigOperators

/-- The completion count from the line structure and the mass bound. -/
theorem completion_count_from_lines {I X : Type} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (T : I → Finset X) (ln : I → I → Finset I) (k : ℕ) (u : ℤ)
    (hkL : k ≤ Fintype.card X)
    (hrefl : ∀ i j, i ≠ j → i ∈ ln i j ∧ j ∈ ln i j)
    (hline : ∀ i j, i ≠ j → (ln i j).card ≤ 11)
    (hnoncol : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → l ∉ ln i j →
      (T i ∩ T j ∩ T l).card ≤ k)
    (hmass : (Fintype.card I : ℤ) * ((Fintype.card X : ℤ) - u) ≤
      ∑ i, ((T i).card : ℤ))
    (hm : 0 < (Fintype.card I : ℤ)) :
    (Fintype.card I : ℤ) *
        (((Fintype.card X : ℤ) - u) ^ 3 - (k : ℤ) * (Fintype.card X : ℤ) ^ 2) ≤
      12 * (Fintype.card X : ℤ) ^ 3 := by
  have hcap := ProximityGap.ThirdMomentCap.third_moment_cap T ln k hkL hrefl hline hnoncol
  exact ProximityGap.CompletionCount.completion_count_bound T ((Fintype.card X : ℤ)) u
    (k : ℤ) 12 rfl hmass hcap hm

/-- Exact values of the first sponsor cutoff. -/
theorem first_sponsor_cutoff_values :
    (311815756 : ℤ) - 62061713 = 249754043 ∧
      (249754043 : ℤ) ^ 3 - 159450661 * 311815756 ^ 2 = 75689626096007542452211 ∧
      (159450661 : ℕ) ≤ 311815756 := by
  norm_num

/-- At the first sponsor cutoff the line structure alone bounds the surviving
heads by `4806`. -/
theorem first_sponsor_completion_from_lines {I X : Type} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] [Nonempty X]
    (T : I → Finset X) (ln : I → I → Finset I)
    (hcardX : (Fintype.card X : ℤ) = 311815756)
    (hrefl : ∀ i j, i ≠ j → i ∈ ln i j ∧ j ∈ ln i j)
    (hline : ∀ i j, i ≠ j → (ln i j).card ≤ 11)
    (hnoncol : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → l ∉ ln i j →
      (T i ∩ T j ∩ T l).card ≤ 159450661)
    (hmass : (Fintype.card I : ℤ) * 249754043 ≤ ∑ i, ((T i).card : ℤ))
    (hm : 0 < (Fintype.card I : ℤ)) :
    (Fintype.card I : ℤ) ≤ 4806 := by
  have hX : Fintype.card X = 311815756 := by
    have h : ((Fintype.card X : ℕ) : ℤ) = ((311815756 : ℕ) : ℤ) := by
      rw [hcardX]
      norm_num
    exact_mod_cast h
  have hkL : 159450661 ≤ Fintype.card X := by omega
  have hLsub : (311815756 : ℤ) - 62061713 = 249754043 := by norm_num
  have hmass' : (Fintype.card I : ℤ) * ((Fintype.card X : ℤ) - 62061713) ≤
      ∑ i, ((T i).card : ℤ) := by
    rw [hcardX, hLsub]
    exact hmass
  have hmain := completion_count_from_lines T ln 159450661 62061713 hkL
    hrefl hline hnoncol hmass' hm
  have hA : (249754043 : ℤ) ^ 3 - 159450661 * 311815756 ^ 2 =
      75689626096007542452211 := by norm_num
  rw [hcardX, hLsub, hA] at hmain
  exact ProximityGap.CompletionCount.first_sponsor_completion_count _ hmain

end ProximityGap.CompletionCountAssembly

#print axioms ProximityGap.CompletionCountAssembly.completion_count_from_lines
#print axioms ProximityGap.CompletionCountAssembly.first_sponsor_cutoff_values
#print axioms ProximityGap.CompletionCountAssembly.first_sponsor_completion_from_lines
