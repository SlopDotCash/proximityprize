/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentTailRateGate

/-!
# Budgeted moment tail-count gate

`_MomentTailRateGate` records the atom-zero version of the finite Markov/union-bound consumer:
an average moment budget proves `X a <= T` for every atom only when the atom count is beaten.

The MCA/list-decoding floor often allows a nonzero bad-scalar budget `B`.  This file records the
corresponding finite last-mile gate:

* if `#α * A < (B + 1) * T^k`, then the number of atoms with `T <= X a` is at most `B`;
* conversely, if the budget can pay for a cluster of `B + 1` atoms at score `S >= T`, then a
  violating cluster-spike model satisfies the same average-moment budget.

Thus positive-proportion or budgeted-tail relaxations do not remove the rate requirement; they only
replace the one-atom threshold by a `B + 1` atom threshold.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.Frontier.MomentTailRateGate

namespace ArkLib.ProximityGap.Frontier.BudgetedMomentTailCountGate

variable {α : Type} [Fintype α]

/-- Weak upper-tail count: atoms with score at least `T`.  This controls the strict tail as well,
and makes the finite Markov gate closed under non-strict moment inequalities. -/
noncomputable def weakTailCount (X : α -> ℝ) (T : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : α => T ≤ X a)).card

/-- The weak tail contributes at least `weakTailCount * T^k` to the unnormalized moment. -/
theorem weakTailCount_mul_threshold_pow_le_powMomentSum
    {X : α -> ℝ} {T : ℝ} {k : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T) :
    (weakTailCount X T : ℝ) * T ^ k ≤ powMomentSum X k := by
  classical
  let s : Finset α := Finset.univ.filter (fun a : α => T ≤ X a)
  have hleft : (s.card : ℝ) * T ^ k = s.sum (fun _a : α => T ^ k) := by
    simp [mul_comm]
  have hsum_le : s.sum (fun _a : α => T ^ k) ≤ s.sum (fun a : α => X a ^ k) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    have hTX : T ≤ X a := by
      exact (Finset.mem_filter.mp ha).2
    exact pow_le_pow_left₀ hT hTX k
  have hsubset : s ⊆ Finset.univ := by
    intro a _ha
    exact Finset.mem_univ a
  have hsubsum : s.sum (fun a : α => X a ^ k) ≤ ∑ a : α, X a ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro a _ha _hnot; exact pow_nonneg (hX a) k)
  have htail :
      (weakTailCount X T : ℝ) * T ^ k = s.sum (fun _a : α => T ^ k) := by
    unfold weakTailCount
    change (s.card : ℝ) * T ^ k = s.sum (fun _a : α => T ^ k)
    exact hleft
  have hmoment :
      s.sum (fun a : α => X a ^ k) ≤ powMomentSum X k := by
    unfold powMomentSum
    exact hsubsum
  calc
    (weakTailCount X T : ℝ) * T ^ k
        = s.sum (fun _a : α => T ^ k) := htail
    _ ≤ s.sum (fun a : α => X a ^ k) := hsum_le
    _ ≤ powMomentSum X k := hmoment

/-- Unnormalized budgeted Markov gate.  If the moment sum is below the contribution of `B + 1`
atoms at threshold `T`, then at most `B` atoms can have score at least `T`. -/
theorem weakTailCount_le_of_powMomentSum_lt_budget
    {X : α -> ℝ} {T : ℝ} {k B : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T)
    (hsum : powMomentSum X k < ((B + 1 : ℕ) : ℝ) * T ^ k) :
    weakTailCount X T ≤ B := by
  by_contra hnot
  have hlt : B < weakTailCount X T := Nat.lt_of_not_ge hnot
  have hsucc : B + 1 ≤ weakTailCount X T := Nat.succ_le_of_lt hlt
  have hscale :
      ((B + 1 : ℕ) : ℝ) * T ^ k
        ≤ (weakTailCount X T : ℝ) * T ^ k := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) (pow_nonneg hT k)
  have hmoment := weakTailCount_mul_threshold_pow_le_powMomentSum
    (X := X) (T := T) (k := k) hX hT
  exact (not_lt_of_ge (le_trans hscale hmoment)) hsum

/-- Average-moment budgeted Markov gate. -/
theorem weakTailCount_le_of_averageMoment_card_mul_lt_budget [Nonempty α]
    {X : α -> ℝ} {T A : ℝ} {k B : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T)
    (havg : powMomentAverage X k ≤ A)
    (hbudget : (Fintype.card α : ℝ) * A < ((B + 1 : ℕ) : ℝ) * T ^ k) :
    weakTailCount X T ≤ B :=
  weakTailCount_le_of_powMomentSum_lt_budget hX hT
    (lt_of_le_of_lt (powMomentSum_le_card_mul_of_average_le (α := α) havg) hbudget)

/-- The score vector supported on a finite cluster has moment sum
`cluster.card * S^k`. -/
theorem powMomentSum_cluster_spike [DecidableEq α]
    (cluster : Finset α) (S : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    powMomentSum (fun a : α => if a ∈ cluster then S else 0) k
      = (cluster.card : ℝ) * S ^ k := by
  classical
  unfold powMomentSum
  calc
    (∑ a : α, (if a ∈ cluster then S else 0) ^ k)
        = ∑ a : α, if a ∈ cluster then S ^ k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          by_cases h : a ∈ cluster
          · simp [h]
          · have hk0 : k ≠ 0 := by omega
            simp [h, hk0]
    _ = (cluster.card : ℝ) * S ^ k := by
          simp [mul_comm]

/-- Average moment of a finite cluster spike. -/
theorem powMomentAverage_cluster_spike [DecidableEq α]
    (cluster : Finset α) (S : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    powMomentAverage (fun a : α => if a ∈ cluster then S else 0) k
      = ((cluster.card : ℝ) * S ^ k) / (Fintype.card α : ℝ) := by
  simp [powMomentAverage, powMomentSum_cluster_spike cluster S hk]

/-- A finite cluster spike has weak-tail count exactly the cluster size when `0 < T <= S`. -/
theorem weakTailCount_cluster_spike [DecidableEq α]
    (cluster : Finset α) {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S) :
    weakTailCount (fun a : α => if a ∈ cluster then S else 0) T = cluster.card := by
  classical
  have hfilter :
      (Finset.univ.filter (fun a : α => T ≤ if a ∈ cluster then S else 0))
        = cluster := by
    ext a
    by_cases ha : a ∈ cluster
    · simp [ha, hTS]
    · simp [ha, not_le.mpr hT]
  unfold weakTailCount
  rw [hfilter]

/-- Cluster-spike obstruction: if the average moment budget can pay for `B + 1` atoms at a score
`S >= T`, then the budget is compatible with more than `B` atoms in the threshold tail. -/
theorem averageMoment_budget_allows_cluster_spike
    {T S A : ℝ} {k B : ℕ} (hk : 1 ≤ k)
    {cluster : Finset α}
    (hcard : cluster.card = B + 1)
    (hS_nonneg : 0 ≤ S) (hT_pos : 0 < T) (hTS : T ≤ S)
    (hbudget : ((cluster.card : ℝ) * S ^ k) / (Fintype.card α : ℝ) ≤ A) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X k ≤ A ∧
      B < weakTailCount X T := by
  classical
  refine ⟨fun a : α => if a ∈ cluster then S else 0, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ cluster
    · simp [ha, hS_nonneg]
    · simp [ha]
  · simpa [powMomentAverage_cluster_spike cluster S hk] using hbudget
  · rw [weakTailCount_cluster_spike cluster hT_pos hTS, hcard]
    omega

/-- Two-sided finite budget gate for moment tails.  The first component is the consumer; the second
component is the finite-cluster obstruction. -/
theorem budgetedMomentTailCountGate
    [Nonempty α]
    {T A : ℝ} {k B : ℕ} (hT_nonneg : 0 ≤ T) (hk : 1 ≤ k) :
    ((Fintype.card α : ℝ) * A < ((B + 1 : ℕ) : ℝ) * T ^ k ->
        ∀ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ->
          powMomentAverage X k ≤ A ->
          weakTailCount X T ≤ B)
      ∧
      (∀ (cluster : Finset α) (S : ℝ),
        cluster.card = B + 1 ->
        0 ≤ S -> 0 < T -> T ≤ S ->
        ((cluster.card : ℝ) * S ^ k) / (Fintype.card α : ℝ) ≤ A ->
        ∃ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ∧
          powMomentAverage X k ≤ A ∧
          B < weakTailCount X T) := by
  constructor
  · intro hbudget X hX havg
    exact weakTailCount_le_of_averageMoment_card_mul_lt_budget
      (α := α) hX hT_nonneg havg hbudget
  · intro cluster S hcard hS hTpos hTS hbudget
    exact averageMoment_budget_allows_cluster_spike
      (α := α) (T := T) (S := S) (A := A) (k := k) (B := B)
      hk hcard hS hTpos hTS hbudget

#print axioms weakTailCount_mul_threshold_pow_le_powMomentSum
#print axioms weakTailCount_le_of_powMomentSum_lt_budget
#print axioms weakTailCount_le_of_averageMoment_card_mul_lt_budget
#print axioms powMomentSum_cluster_spike
#print axioms powMomentAverage_cluster_spike
#print axioms weakTailCount_cluster_spike
#print axioms averageMoment_budget_allows_cluster_spike
#print axioms budgetedMomentTailCountGate

end ArkLib.ProximityGap.Frontier.BudgetedMomentTailCountGate
