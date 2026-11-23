/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._IncidenceTripleMass
import ArkLib.Research.ProximityGap.Frontier._PairUnionMomentMean

/-!
# The completion count from a third-moment cap

The reciprocal-locator argument restricts to a set of `L` coordinates and
considers the `m` surviving locator heads, each with at most `u` errors there.
Any three distinct heads share at most `k` agreements, so the third moment of
the agreement degrees obeys `∑ f ^ 3 ≤ k m ^ 3 + C L m ^ 2` for a small `C`
that charges the repeated indices and the collinear exceptions.

This module turns that cap into the completion bound. Jensen gives
`(∑ f) ^ 3 ≤ L ^ 2 ∑ f ^ 3`, the mass bound gives `m (L - u) ≤ ∑ f`, and
cancelling `m ^ 2` leaves

`m ((L - u) ^ 3 - k L ^ 2) ≤ C L ^ 3`.

At the first sponsor radius, with `C = 12` and the draft's cutoff, the exact
margin bounds `m` by `4806`. That is stronger than the draft's `6830` because
it keeps `L` instead of replacing it by `2 t`.

The geometric construction of the locator heads, the triple cap and the line
cap remain written arguments; this module proves the counting step that
consumes them.
-/

set_option autoImplicit false

namespace ProximityGap.CompletionCount

open scoped BigOperators

/-- Jensen for the cube of a sum, in integer form. -/
theorem cube_sum_le_card_sq_mul_sum_cube_int {X : Type*} [Fintype X] (f : X → ℤ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x, f x) ^ 3 ≤ (Fintype.card X : ℤ) ^ 2 * ∑ x, f x ^ 3 := by
  have h := ProximityGap.IncidenceTripleMass.nat_cube_sum_le_card_sq_mul_sum_cube
    (fun x => (f x).toNat)
  have hcast : ((∑ x, (f x).toNat : ℕ) : ℤ) ^ 3 ≤
      ((Fintype.card X : ℕ) : ℤ) ^ 2 * (((∑ x, ((f x).toNat) ^ 3 : ℕ)) : ℤ) := by
    exact_mod_cast h
  have h1 : ((∑ x, (f x).toNat : ℕ) : ℤ) = ∑ x, f x := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun x _ => Int.toNat_of_nonneg (hf x)
  have h2 : (((∑ x, ((f x).toNat) ^ 3 : ℕ)) : ℤ) = ∑ x, f x ^ 3 := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Nat.cast_pow, Int.toNat_of_nonneg (hf x)]
  rw [h1, h2] at hcast
  exact hcast

/-- The completion bound: a third-moment cap and a mass bound force a small
number of surviving heads. -/
theorem completion_count_bound {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (T : I → Finset X) (L u k C : ℤ)
    (hL : (Fintype.card X : ℤ) = L)
    (hmass : (Fintype.card I : ℤ) * (L - u) ≤ ∑ i, ((T i).card : ℤ))
    (h3 : ∑ x, (ProximityGap.PairUnionMoment.degree T x) ^ 3 ≤
      k * (Fintype.card I : ℤ) ^ 3 + C * L * (Fintype.card I : ℤ) ^ 2)
    (hm : 0 < (Fintype.card I : ℤ)) :
    (Fintype.card I : ℤ) * ((L - u) ^ 3 - k * L ^ 2) ≤ C * L ^ 3 := by
  classical
  set m : ℤ := (Fintype.card I : ℤ) with hmm
  set S : ℤ := ∑ x, ProximityGap.PairUnionMoment.degree T x with hS
  have hmass' : m * (L - u) ≤ S := by
    rw [hmm, hS]
    exact hmass.trans (le_of_eq (ProximityGap.PairUnionMoment.sum_card_eq_sum_degree T))
  have h3' : ∑ x, (ProximityGap.PairUnionMoment.degree T x) ^ 3 ≤
      k * m ^ 3 + C * L * m ^ 2 := by
    rw [hmm]
    exact h3
  have hjensen : S ^ 3 ≤ L ^ 2 * ∑ x, (ProximityGap.PairUnionMoment.degree T x) ^ 3 := by
    have h := cube_sum_le_card_sq_mul_sum_cube_int
      (fun x => ProximityGap.PairUnionMoment.degree T x)
      (fun x => ProximityGap.PairUnionMoment.degree_nonneg T x)
    rw [hL] at h
    rw [hS]
    exact h
  have hmono : (m * (L - u)) ^ 3 ≤ S ^ 3 := pow_le_pow_left' hmass' 3
  have hcube : (m * (L - u)) ^ 3 ≤ L ^ 2 * (k * m ^ 3 + C * L * m ^ 2) := by
    refine hmono.trans ?_
    exact hjensen.trans (mul_le_mul_of_nonneg_left h3' (by nlinarith [sq_nonneg L]))
  have hexp : (m * (L - u)) ^ 3 = m ^ 3 * (L - u) ^ 3 := by ring
  rw [hexp] at hcube
  have hkey : m ^ 3 * ((L - u) ^ 3 - k * L ^ 2) ≤ C * L ^ 3 * m ^ 2 := by
    nlinarith [hcube]
  have hm2 : (0 : ℤ) < m ^ 2 := pow_pos hm 2
  have hcancel : m * ((L - u) ^ 3 - k * L ^ 2) ≤ C * L ^ 3 :=
    le_of_mul_le_mul_left (a := m ^ 2) (b := m * ((L - u) ^ 3 - k * L ^ 2))
      (c := C * L ^ 3) (by nlinarith [hkey]) hm2
  rw [← hmm]
  exact hcancel

/-- Exact values at the first sponsor cutoff: the restricted width, the
agreement cap, the error allowance and the surviving margin. -/
theorem first_sponsor_completion_margin :
    (311815756 : ℤ) - 62061713 = 249754043 ∧
      (249754043 : ℤ) ^ 3 - 159450661 * 311815756 ^ 2 = 75689626096007542452211 ∧
      0 < 75689626096007542452211 ∧
      12 * 311815756 ^ 3 < 4807 * 75689626096007542452211 := by
  norm_num

/-- At the first sponsor cutoff the surviving heads number at most `4806`. -/
theorem first_sponsor_completion_count (m : ℤ) (hm : 0 < m)
    (h : m * 75689626096007542452211 ≤ 12 * 311815756 ^ 3) : m ≤ 4806 := by
  have hA : (0 : ℤ) < 75689626096007542452211 := by norm_num
  have hC : 12 * 311815756 ^ 3 < 4807 * 75689626096007542452211 := by norm_num
  nlinarith [h, hA, hC]

end ProximityGap.CompletionCount

#print axioms ProximityGap.CompletionCount.cube_sum_le_card_sq_mul_sum_cube_int
#print axioms ProximityGap.CompletionCount.completion_count_bound
#print axioms ProximityGap.CompletionCount.first_sponsor_completion_margin
#print axioms ProximityGap.CompletionCount.first_sponsor_completion_count
