/-
Copyright (c) 2026 Jonas Augustinus Linus. All rights reserved.
Released under MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Jonas Augustinus Linus (@Jonas-Augustinus-Linus)
-/
import Mathlib

set_option autoImplicit false

namespace ProximityGap.IncidenceFourthMomentDirectBound

set_option maxRecDepth 4096

/-!
This file audits a direct fourth-moment replacement for the canonical sponsor
cube argument. With `n = 2^30` coordinates and `m = n+1` witnesses, use the
line-cap-three fact to say every four-distinct tuple has error union at least
`d+1`, while every tuple with at least two distinct indices has error union at
least `d+1-t` by the pair-union distance lemma. A one-index tuple contributes
the trivial lower bound zero.

The fourth-moment upper bound is the usual power-mean bound from errors of size
at most `t`. The theorem below computes the exact point where these two scalar
inequalities cease to contradict one another. This is only a limitation of
this direct fourth-moment argument, not a counterexample to the canonical code
or the prize statement.
-/

/-- Production coordinate count in the first-sponsor finite bracket. -/
private def n : ℕ := 2 ^ 30

/-- Number of distinct scalar witnesses at this instance. -/
private def m : ℕ := n + 1

/-- Reed--Solomon support distance parameter for this instance. -/
private def d : ℕ := 2 ^ 29

/-- Largest error count for which the direct scalar inequalities contradict. -/
private def cutoff : ℕ := 170836173

/-- Ordered four-tuples with pairwise distinct witness indices. -/
private def fourDistinct : ℕ := m * (m - 1) * (m - 2) * (m - 3)

/-- Direct lower mass from the four-distinct and pair-union distance bounds. -/
private def directLower (t : ℕ) : ℕ :=
  fourDistinct * (d + 1) + (m ^ 4 - m - fourDistinct) * (d + 1 - t)

/-- Fourth-power complement upper mass when each witness has at most `t` errors. -/
private def fourthMomentUpper (t : ℕ) : ℕ :=
  n ^ 4 * m ^ 4 - m ^ 4 * (n - t) ^ 4

/-- The distinct-fourth-moment bound has no contradiction above the incumbent
canonical floor: at the existing error budget, its upper moment already
dominates its strongest direct lower bound from pair-distance and line-cap
three. The positive `slack` is exact, not a floating-point approximation. -/
theorem direct_fourth_moment_does_not_reach_incumbent_floor :
    directLower 221512373 * n ^ 3 < fourthMomentUpper 221512373 := by
  norm_num [directLower, fourthMomentUpper, fourDistinct, n, m, d]

/-- The exact integer crossing is between 170836173 and 170836174 errors. -/
theorem direct_fourth_moment_cutoff_is_exact :
    fourthMomentUpper cutoff < directLower cutoff * n ^ 3 ∧
      directLower (cutoff + 1) * n ^ 3 < fourthMomentUpper (cutoff + 1) := by
  norm_num [cutoff, directLower, fourthMomentUpper, fourDistinct, n, m, d]

/-- If the direct fourth-moment inequalities are consistent for a candidate
bad family, its error budget must exceed `170836173`. Thus this argument alone
cannot reach the existing first-sponsor floor `221512374`. -/
theorem consistent_direct_fourth_moment_budget_exceeds_cutoff
    {t : ℕ}
    (hconsistent : directLower t * n ^ 3 ≤ fourthMomentUpper t) :
    cutoff < t := by
  by_contra hnot
  have htold : t ≤ cutoff := by omega
  have hsub : d + 1 - cutoff ≤ d + 1 - t :=
    Nat.sub_le_sub_left htold (d + 1)
  have hlow : directLower cutoff ≤ directLower t := by
    unfold directLower
    have hmul := Nat.mul_le_mul_left (m ^ 4 - m - fourDistinct) hsub
    exact Nat.add_le_add_left hmul _
  have hbase : n - cutoff ≤ n - t := Nat.sub_le_sub_left htold n
  have hpow : (n - cutoff) ^ 4 ≤ (n - t) ^ 4 := by
    exact Nat.pow_le_pow_left hbase 4
  have hmul : m ^ 4 * (n - cutoff) ^ 4 ≤ m ^ 4 * (n - t) ^ 4 :=
    Nat.mul_le_mul_left _ hpow
  have hupp : fourthMomentUpper t ≤ fourthMomentUpper cutoff := by
    unfold fourthMomentUpper
    exact Nat.sub_le_sub_left hmul _
  have hexact : fourthMomentUpper cutoff < directLower cutoff * n ^ 3 := by
    exact direct_fourth_moment_cutoff_is_exact.1
  have hchain : directLower cutoff * n ^ 3 ≤ fourthMomentUpper cutoff :=
    le_trans (Nat.mul_le_mul_right (n ^ 3) hlow) (le_trans hconsistent hupp)
  exact (not_le_of_gt hexact) hchain

#print axioms direct_fourth_moment_does_not_reach_incumbent_floor
#print axioms direct_fourth_moment_cutoff_is_exact
#print axioms consistent_direct_fourth_moment_budget_exceeds_cutoff

end ProximityGap.IncidenceFourthMomentDirectBound
