/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib

/-!
# The ordered-pair agreement moment and the mean pair error-union bound

The pair-weighted reciprocal-locator argument fixes a pair of heads and counts
the completions of that pair. Summing that local count over all pairs needs a
lower bound on the *mean* error-union size of a pair. This module derives the
bound instead of assuming it.

Three exact ledgers are proved for an arbitrary family of agreement sets:

* the ordered pair-intersection mass is the sum of the squared agreement
  degrees,
* subtracting the diagonal turns it into the falling square `M (M - 1)`, which
  is exactly the complement of the ordered pair-union mass,
* a single pointwise inequality `3 q M ^ 2 ≤ 2 M ^ 3 + q ^ 3` charges the
  squared mass to the cube mass.

Together they turn any upper bound on the third moment of the agreement
degrees and any lower bound on their total mass into an upper bound on the
falling square, hence into the mean pair-union bound that the weighted locator
certificate consumes.

The local completion count, the aggregate over pairs, and the transfer of this
mean bound into a sponsor-facing floor remain open obligations.
-/

set_option autoImplicit false

namespace ProximityGap.PairUnionMoment

open scoped BigOperators

/-- The agreement degree of a coordinate: how many heads agree there. -/
def degree {I X : Type*} [Fintype I] [DecidableEq X] (T : I → Finset X) (x : X) : ℤ :=
  ∑ i, (if x ∈ T i then (1 : ℤ) else 0)

/-- The agreement degree is nonnegative. -/
theorem degree_nonneg {I X : Type*} [Fintype I] [DecidableEq X] (T : I → Finset X) (x : X) :
    0 ≤ degree T x := by
  rw [degree]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : x ∈ T i <;> simp [h]

/-- Total agreement mass equals the sum of the agreement degrees. -/
theorem sum_card_eq_sum_degree {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (T : I → Finset X) :
    (∑ i, ((T i).card : ℤ)) = ∑ x, degree T x := by
  classical
  have hterm : ∀ i, ((T i).card : ℤ) = ∑ x, (if x ∈ T i then (1 : ℤ) else 0) := by
    intro i
    have hfilter : (Finset.univ.filter (fun x => x ∈ T i)) = T i := by
      ext x
      simp
    rw [← hfilter, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x ∈ T i <;> simp [h]
  simp only [hterm, degree]
  exact Finset.sum_comm

/-- The ordered pair-intersection mass is the sum of squared agreement degrees. -/
theorem sum_card_inter_eq_sum_degree_sq {I X : Type*} [Fintype I] [Fintype X]
    [DecidableEq X] (T : I → Finset X) :
    (∑ i, ∑ j, ((T i ∩ T j).card : ℤ)) = ∑ x, (degree T x) ^ 2 := by
  classical
  have hterm : ∀ i j, ((T i ∩ T j).card : ℤ) =
      ∑ x, (if x ∈ T i then (1 : ℤ) else 0) * (if x ∈ T j then (1 : ℤ) else 0) := by
    intro i j
    have hfilter : (Finset.univ.filter (fun x => x ∈ T i ∩ T j)) = T i ∩ T j := by
      ext x
      simp
    rw [← hfilter, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hi : x ∈ T i <;> by_cases hj : x ∈ T j <;> simp [hi, hj]
  have hswap : (∑ i, ∑ j, ∑ x,
        (if x ∈ T i then (1 : ℤ) else 0) * (if x ∈ T j then (1 : ℤ) else 0)) =
      ∑ x, ∑ i, ∑ j,
        (if x ∈ T i then (1 : ℤ) else 0) * (if x ∈ T j then (1 : ℤ) else 0) := by
    calc
      _ = ∑ i, ∑ x, ∑ j,
            (if x ∈ T i then (1 : ℤ) else 0) * (if x ∈ T j then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [hterm, hswap]
  apply Finset.sum_congr rfl
  intro x _
  simp only [degree, pow_two]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Distinct ordered pairs: the falling square of the agreement degree. -/
theorem sum_card_inter_erase_eq_sum_degree_mul_pred {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] (T : I → Finset X) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i, ((T i ∩ T j).card : ℤ)) =
      ∑ x, degree T x * (degree T x - 1) := by
  classical
  have hsplit : ∀ i, (∑ j ∈ (Finset.univ : Finset I).erase i, ((T i ∩ T j).card : ℤ)) =
      (∑ j, ((T i ∩ T j).card : ℤ)) - ((T i).card : ℤ) := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.inter_self]
  have hfalling : (∑ x, degree T x * (degree T x - 1)) =
      ∑ x, (degree T x) ^ 2 - ∑ x, degree T x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, sum_card_inter_eq_sum_degree_sq, sum_card_eq_sum_degree,
    hfalling]

/-- Pointwise form of the third-moment slack used by the mean bound. -/
theorem three_mul_sq_le (m q : ℤ) (hm : 0 ≤ m) (hq : 0 < q) :
    3 * q * m ^ 2 ≤ 2 * m ^ 3 + q ^ 3 := by
  have hfactor : (m - q) ^ 2 * (2 * m + q) = 2 * m ^ 3 - 3 * m ^ 2 * q + q ^ 3 := by
    ring
  have hnonneg : 0 ≤ (m - q) ^ 2 * (2 * m + q) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  rw [hfactor] at hnonneg
  linarith

/-- Summed third-moment slack: the squared mass is charged to the cube mass. -/
theorem sum_three_mul_sq_le {X : Type*} [Fintype X] (M : X → ℤ) (q U : ℤ)
    (hM : ∀ x, 0 ≤ M x) (hq : 0 < q) (h3 : ∑ x, M x ^ 3 ≤ U) :
    3 * q * ∑ x, M x ^ 2 ≤ 2 * U + (Fintype.card X : ℤ) * q ^ 3 := by
  have hpoint : ∀ x ∈ (Finset.univ : Finset X), 3 * q * M x ^ 2 ≤ 2 * M x ^ 3 + q ^ 3 :=
    fun x _ => three_mul_sq_le (M x) q (hM x) hq
  have hsum := Finset.sum_le_sum hpoint
  have hleft : (∑ x, (3 * q * M x ^ 2)) = 3 * q * ∑ x, M x ^ 2 := by
    rw [Finset.mul_sum]
  have hright : (∑ x, (2 * M x ^ 3 + q ^ 3)) =
      2 * ∑ x, M x ^ 3 + (Fintype.card X : ℤ) * q ^ 3 := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hleft, hright] at hsum
  nlinarith [h3, hsum]

/-- The ordered pair-union mass is the total pair count minus the falling square. -/
theorem ordered_pair_union_deficit {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (T : I → Finset X) :
    (Fintype.card I : ℤ) * ((Fintype.card I : ℤ) - 1) * (Fintype.card X : ℤ) -
        (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (((Finset.univ : Finset X) \ (T i ∩ T j)).card : ℤ)) =
      ∑ x, degree T x * (degree T x - 1) := by
  classical
  have hcard : ∀ i j, (((Finset.univ : Finset X) \ (T i ∩ T j)).card : ℤ) =
      (Fintype.card X : ℤ) - ((T i ∩ T j).card : ℤ) := by
    intro i j
    have h := Finset.card_sdiff_add_card_eq_card
      (s := T i ∩ T j) (t := (Finset.univ : Finset X)) (Finset.subset_univ _)
    have h' : (((Finset.univ : Finset X) \ (T i ∩ T j)).card : ℤ) +
        ((T i ∩ T j).card : ℤ) = (Fintype.card X : ℤ) := by
      rw [← Nat.cast_add, h, Finset.card_univ]
    linarith
  have hinner : ∀ i, (∑ j ∈ (Finset.univ : Finset I).erase i,
        ((Fintype.card X : ℤ) - ((T i ∩ T j).card : ℤ))) =
      ((Fintype.card I : ℤ) - 1) * (Fintype.card X : ℤ) -
        ∑ j ∈ (Finset.univ : Finset I).erase i, ((T i ∩ T j).card : ℤ) := by
    intro i
    have hpos : 1 ≤ Fintype.card I := Finset.card_pos.mpr ⟨i, Finset.mem_univ i⟩
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, nsmul_eq_mul,
      Nat.cast_sub hpos]
    ring
  simp only [hcard, hinner]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    sum_card_inter_erase_eq_sum_degree_mul_pred]
  ring

/-- Mean pair-union ledger: an upper third moment and a lower agreement mass
bound the falling square, hence the ordered pair-union total. -/
theorem mean_pair_union_moment {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (T : I → Finset X) (q g U : ℤ) (hq : 0 < q)
    (h3 : ∑ x, (degree T x) ^ 3 ≤ U) (hg : g ≤ ∑ x, degree T x) :
    3 * q * ((Fintype.card I : ℤ) * ((Fintype.card I : ℤ) - 1) * (Fintype.card X : ℤ) -
        (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (((Finset.univ : Finset X) \ (T i ∩ T j)).card : ℤ)) + g) ≤
      2 * U + (Fintype.card X : ℤ) * q ^ 3 := by
  classical
  have hfalling : (∑ x, degree T x * (degree T x - 1)) =
      ∑ x, (degree T x) ^ 2 - ∑ x, degree T x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [ordered_pair_union_deficit, hfalling]
  have hsq := sum_three_mul_sq_le (fun x => degree T x) q U
    (fun x => degree_nonneg T x) hq h3
  have hle : ∑ x, (degree T x) ^ 2 - ∑ x, degree T x + g ≤ ∑ x, (degree T x) ^ 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℤ) ≤ 3 * q)
  linarith

/-- The mean pair-union bound in the division-free form the weighted locator
certificate consumes: the total pair-union mass is at least
`n + (g - (2 U + n q^3)/(3 q)) / (b (b-1))` pairs, written as one integer
inequality. -/
theorem mean_pair_union_ge {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (T : I → Finset X) (q g U : ℤ) (hq : 0 < q)
    (h3 : ∑ x, (degree T x) ^ 3 ≤ U) (hg : g ≤ ∑ x, degree T x) :
    3 * q * (Fintype.card I : ℤ) * ((Fintype.card I : ℤ) - 1) * (Fintype.card X : ℤ) -
        (2 * U + (Fintype.card X : ℤ) * q ^ 3) + 3 * q * g ≤
      3 * q * (∑ i, ∑ j ∈ (Finset.univ : Finset I).erase i,
        (((Finset.univ : Finset X) \ (T i ∩ T j)).card : ℤ)) := by
  have h := mean_pair_union_moment T q g U hq h3 hg
  nlinarith [h]

/-- Exact arithmetic for the pair-weighted locator certificate at the successor
radius `223580000`. The mean surplus per unordered triple is compared with the
*exact* ledger gap `3898096` instead of the round `3800000` used at the
published radius, so a single round bound `3900000` still separates the surplus
from the gap. -/
theorem first_sponsor_weighted_locator_margins_successor :
    let n : ℤ := 1073741824
    let D : ℤ := 536870913
    let t : ℤ := 223580000
    let a : ℤ := 397300000
    let q : ℤ := 852000000
    let b := n + 1
    let l := D - 2 * t
    let s := a - t
    let g := b * (n - t)
    let ordered := b * (b - 1) * (b - 2)
    let U := (n - D) * ordered + 2 * D * b + 3 * n * b ^ 2
    let denom := 3 * q * b * (b - 1)
    let meanNum := n * denom - 2 * U - n * q ^ 3 + 3 * q * g
    let Y := 4 * s ^ 3
    let slope := 5 * s ^ 3 - 3 * l ^ 2 * s - 2 * l ^ 3
    let W := fun e : ℤ => s * (s + l) ^ 3 - (D - a) * Y + slope * (e - a)
    0 < slope ∧ W t < 100000 * Y ∧
    W (2 * t) - 100000 * Y < 3 * 20233795 * Y ∧ n < 16 * l - 8 * 20233794 ∧
    17 * 2 * t < 80000 * 100000 ∧ 397323129 * denom < meanNum ∧
    3900000 * (b - 2) * 3 * Y < (b - 2 - 80003) * (W 397323129 - 100003 * Y) ∧
    n ^ 2 * ((n - D) * ordered + 2 * D * b) - g * (g - n) * (g - 2 * n) <
      3900000 * n ^ 2 * ordered := by
  norm_num

end ProximityGap.PairUnionMoment

#print axioms ProximityGap.PairUnionMoment.degree_nonneg
#print axioms ProximityGap.PairUnionMoment.sum_card_eq_sum_degree
#print axioms ProximityGap.PairUnionMoment.sum_card_inter_eq_sum_degree_sq
#print axioms ProximityGap.PairUnionMoment.sum_card_inter_erase_eq_sum_degree_mul_pred
#print axioms ProximityGap.PairUnionMoment.three_mul_sq_le
#print axioms ProximityGap.PairUnionMoment.sum_three_mul_sq_le
#print axioms ProximityGap.PairUnionMoment.ordered_pair_union_deficit
#print axioms ProximityGap.PairUnionMoment.mean_pair_union_moment
#print axioms ProximityGap.PairUnionMoment.mean_pair_union_ge
#print axioms ProximityGap.PairUnionMoment.first_sponsor_weighted_locator_margins_successor
