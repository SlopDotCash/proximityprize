/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic

/-!
# Exact third moment without replacement at the first sponsor radius

The agreement incidence moment uses ordered triples of distinct heads.
A supporting-line inequality for the falling cubic keeps its quadratic and
linear terms, including at coordinates with fewer than three agreements.
-/

open scoped BigOperators

namespace ProximityGap.IncidenceDistinctTripleMoment

private theorem choose_three_int (m : ℕ) :
    (6 : ℤ) * m.choose 3 = (m : ℤ) * (m - 1 : ℤ) * (m - 2 : ℤ) := by
  by_cases hm : 2 ≤ m
  · have h2 := Nat.choose_succ_right_eq m 1
    have h3 := Nat.choose_succ_right_eq m 2
    norm_num [Nat.choose_one_right] at h2 h3
    have h : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
      calc
        _ = 2 * (m.choose 3 * 3) := by ring
        _ = 2 * (m.choose 2 * (m - 2)) := by rw [h3]
        _ = (m.choose 2 * 2) * (m - 2) := by ring
        _ = _ := by rw [h2]
    have hz := congrArg (fun k : ℕ ↦ (k : ℤ)) h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ m),
      Nat.cast_sub hm] using hz
  · have h : m = 0 ∨ m = 1 := by omega
    rcases h with rfl | rfl
    all_goals decide

/-- Scaled Jensen lower bound for the exact distinct-triple incidence mass.
The target agreement mass g may be any lower bound on the true mass. -/
theorem falling_cubic_lower {X : Type*} [Fintype X] (m : X → ℕ) (g : ℤ)
    (hn : 0 < Fintype.card X)
    (hg : 2 * (Fintype.card X : ℤ) ≤ g)
    (hm : g ≤ ∑ x, (m x : ℤ)) :
    g * (g - Fintype.card X) * (g - 2 * Fintype.card X) ≤
      (Fintype.card X : ℤ)^2 * (6 * ∑ x, (m x).choose 3) := by
  let n : ℤ := Fintype.card X
  let f : ℤ → ℤ := fun z ↦ z * (z - n) * (z - 2 * n)
  change 2 * n ≤ g at hg
  let slope : ℤ := 3 * (g - n)^2 - n^2
  have hn' : 0 < n := by
    change (0 : ℤ) < (Fintype.card X : ℤ)
    exact_mod_cast hn
  have hs : 0 ≤ slope := by
    dsimp [slope]
    have h : 0 ≤ (g - 2 * n) * g := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg n]
  have point (x : X) : f g + slope * (n * (m x : ℤ) - g) ≤ f (n * m x) := by
    have hfactor : 0 ≤ n * (m x : ℤ) + 2 * g - 3 * n := by
      have h := mul_nonneg hn'.le (Int.natCast_nonneg (m x))
      omega
    have h := mul_nonneg (sq_nonneg (n * (m x : ℤ) - g)) hfactor
    dsimp [f, slope]
    nlinarith only [h]
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ point x)
  have scale (x : X) : f (n * (m x : ℤ)) = n^3 * (6 * ((m x).choose 3 : ℤ)) := by
    rw [choose_three_int]
    dsimp [f]
    ring
  simp only [scale, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at summed
  change n * f g + slope * (n * (∑ x, (m x : ℤ)) - n * g) ≤
    n^3 * (6 * ∑ x, ((m x).choose 3 : ℤ)) at summed
  have nonneg : 0 ≤ slope * (n * (∑ x, (m x : ℤ)) - n * g) :=
    mul_nonneg hs (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hm hn'.le))
  have bound : n * f g ≤ n * (n^2 * (6 * ∑ x, ((m x).choose 3 : ℤ))) := by
    calc
      _ ≤ n * f g + slope * (n * (∑ x, (m x : ℤ)) - n * g) := by omega
      _ ≤ _ := summed.trans_eq (by ring)
  push_cast
  change f g ≤ n^2 * (6 * ∑ x, ((m x).choose 3 : ℤ))
  by_contra! bad
  exact (not_lt_of_ge bound) (mul_lt_mul_of_pos_left bad hn')

/-- Even after deleting the entire collinear penalty, the distinct-triple
ledger does not give a contradiction at radius numerator 221512374. -/
theorem first_sponsor_distinct_triple_ledger_has_slack :
    let n : ℤ := 1073741824
    let b : ℤ := n + 1
    let g : ℤ := b * (n - 221512374)
    g * (g - n) * (g - 2 * n) <
      n^2 * ((n - 536870913) * b * (b - 1) * (b - 2)) := by
  norm_num

/-- An excess of one error coordinate on 30% of all unordered triples suffices
at the successor radius, even charging the maximum possible contribution to
each of the at most `b / 3` collinear triples. -/
theorem first_sponsor_distinct_triple_excess_target :
    let n : ℤ := 1073741824
    let b : ℤ := n + 1
    let D : ℤ := 536870913
    let g : ℤ := b * (n - 221512374)
    let total : ℤ := b * (b - 1) * (b - 2) / 6
    let excess : ℤ := 3 * total / 10
    6 * n^2 * ((n - D) * total + D * (b / 3) - excess) <
      g * (g - n) * (g - 2 * n) := by
  norm_num

end ProximityGap.IncidenceDistinctTripleMoment

#print axioms ProximityGap.IncidenceDistinctTripleMoment.falling_cubic_lower
#print axioms ProximityGap.IncidenceDistinctTripleMoment.first_sponsor_distinct_triple_ledger_has_slack
#print axioms ProximityGap.IncidenceDistinctTripleMoment.first_sponsor_distinct_triple_excess_target
