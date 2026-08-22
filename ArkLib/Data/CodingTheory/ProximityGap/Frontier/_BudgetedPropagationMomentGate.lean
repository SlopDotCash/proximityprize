/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BudgetedMomentTailCountGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PropagationTailGate

/-!
# Budgeted moment tails need propagation to become pointwise bounds

`_BudgetedMomentTailCountGate` proves the finite Markov last-mile statement: a `k`-th average
moment budget can bound the number of atoms above a threshold by `B` exactly when the budget is
below the contribution of `B + 1` threshold atoms.

`_PropagationTailGate` proves the anti-spike conversion: if every nonempty bad tail propagates to
at least `s` bad atoms, then a tail count below `s` is a pointwise exclusion.

This file combines the two.  It is the clean finite form of the issue #464 vertical-Sato-Tate
last mile:

* moment information alone only buys a budgeted tail count;
* a pointwise/sup theorem additionally needs an anti-spike propagation theorem at the same cluster
  scale;
* the cluster-spike model shows the bound is sharp when the moment budget can pay for one full
  propagated cluster.

No Gauss-period propagation theorem is asserted here.  The new mathematical burden remains exactly
the missing relation-level anti-spike input for the Paley spectrum / far-line incidence family.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.Frontier.BudgetedMomentTailCountGate
open ArkLib.ProximityGap.Frontier.MomentTailRateGate
open ArkLib.ProximityGap.Frontier.PropagationTailGate

namespace ArkLib.ProximityGap.Frontier.BudgetedPropagationMomentGate

variable {α : Type} [Fintype α]

/-- The threshold-bad predicate associated to a score function. -/
def scoreBad (X : α -> ℝ) (T : ℝ) : α -> Prop :=
  fun a : α => T ≤ X a

/-- The propagation-gate bad count for `scoreBad` is the budgeted weak-tail count. -/
theorem badCount_scoreBad_eq_weakTailCount (X : α -> ℝ) (T : ℝ) :
    badCount (scoreBad X T) = weakTailCount X T := by
  classical
  letI : DecidablePred (fun a : α => T ≤ X a) := Classical.decPred _
  unfold badCount weakTailCount scoreBad
  rfl

/-- Moment budget + minimum propagated bad-tail size gives a pointwise strict threshold bound. -/
theorem forall_lt_threshold_of_budgetedMoment_and_minimumTailCard [Nonempty α]
    {X : α -> ℝ} {T A : ℝ} {k B : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T)
    (havg : powMomentAverage X k ≤ A)
    (hbudget : (Fintype.card α : ℝ) * A < ((B + 1 : ℕ) : ℝ) * T ^ k)
    (hmin : MinimumBadTailCard (scoreBad X T) (B + 1)) :
    ∀ a : α, X a < T := by
  have htail : weakTailCount X T ≤ B :=
    weakTailCount_le_of_averageMoment_card_mul_lt_budget
      (α := α) hX hT havg hbudget
  have hbadCount : badCount (scoreBad X T) < B + 1 := by
    rw [badCount_scoreBad_eq_weakTailCount]
    omega
  have hnoBad : ∀ a : α, ¬ scoreBad X T a :=
    forall_not_of_badCount_lt_minimumCard
      (Bad := scoreBad X T) (s := B + 1) hmin hbadCount
  intro a
  exact lt_of_not_ge (hnoBad a)

/-- Relation-level version: a propagation relation creating `B + 1` bad atoms upgrades the
budgeted Markov tail count to a pointwise strict bound. -/
theorem forall_lt_threshold_of_budgetedMoment_and_badPropagates [Nonempty α]
    {X : α -> ℝ} {T A : ℝ} {k B : ℕ} {R : α -> α -> Prop}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T)
    (havg : powMomentAverage X k ≤ A)
    (hbudget : (Fintype.card α : ℝ) * A < ((B + 1 : ℕ) : ℝ) * T ^ k)
    (hprop : BadPropagates R (scoreBad X T) (B + 1)) :
    ∀ a : α, X a < T :=
  forall_lt_threshold_of_budgetedMoment_and_minimumTailCard
    (α := α) hX hT havg hbudget (minimumBadTailCard_of_badPropagates hprop)

/-- The relation that makes a finite cluster propagate internally. -/
def clusterRelation (cluster : Finset α) : α -> α -> Prop :=
  fun a b : α => a ∈ cluster ∧ b ∈ cluster

/-- For a cluster spike, the internally propagated bad neighborhood is exactly the cluster. -/
theorem badNeighborhoodCount_clusterSpike_clusterRelation [DecidableEq α]
    (cluster : Finset α) {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S) {a : α}
    (ha : a ∈ cluster) :
    badNeighborhoodCount (clusterRelation cluster)
        (scoreBad (fun b : α => if b ∈ cluster then S else 0) T) a
      = cluster.card := by
  classical
  have hfilter :
      (Finset.univ.filter
          (fun b : α =>
            clusterRelation cluster a b ∧
              scoreBad (fun c : α => if c ∈ cluster then S else 0) T b))
        = cluster := by
    ext b
    by_cases hb : b ∈ cluster
    · simp [clusterRelation, scoreBad, ha, hb, hTS]
    · simp [clusterRelation, scoreBad, hb, not_le.mpr hT]
  unfold badNeighborhoodCount
  rw [hfilter]

/-- A cluster spike satisfies the relation-level propagation hypothesis at exactly the cluster
size. -/
theorem clusterSpike_badPropagates_clusterRelation [DecidableEq α]
    (cluster : Finset α) {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S) :
    BadPropagates (clusterRelation cluster)
      (scoreBad (fun b : α => if b ∈ cluster then S else 0) T) cluster.card := by
  intro a haBad
  have ha : a ∈ cluster := by
    by_contra hnot
    have hzero : ¬ scoreBad (fun b : α => if b ∈ cluster then S else 0) T a := by
      simp [scoreBad, hnot, not_le.mpr hT]
    exact hzero haBad
  rw [badNeighborhoodCount_clusterSpike_clusterRelation cluster hT hTS ha]

/-- Sharp obstruction: if the average-moment budget can pay for a full propagated cluster of
`B + 1` threshold atoms, then a propagating cluster spike is compatible with the same moment budget
and violates the desired `B`-tail conclusion. -/
theorem averageMoment_budget_allows_propagating_cluster_spike
    {T S A : ℝ} {k B : ℕ} (hk : 1 ≤ k)
    {cluster : Finset α}
    (hcard : cluster.card = B + 1)
    (hS_nonneg : 0 ≤ S) (hT_pos : 0 < T) (hTS : T ≤ S)
    (hbudget : ((cluster.card : ℝ) * S ^ k) / (Fintype.card α : ℝ) ≤ A) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X k ≤ A ∧
      B < weakTailCount X T ∧
      BadPropagates (clusterRelation cluster) (scoreBad X T) (B + 1) := by
  classical
  refine ⟨fun a : α => if a ∈ cluster then S else 0, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ cluster
    · simp [ha, hS_nonneg]
    · simp [ha]
  · simpa [powMomentAverage_cluster_spike cluster S hk] using hbudget
  · rw [weakTailCount_cluster_spike cluster hT_pos hTS, hcard]
    omega
  · simpa [hcard] using
      clusterSpike_badPropagates_clusterRelation
        (cluster := cluster) (T := T) (S := S) hT_pos hTS

/-- Two-sided finite gate.  Below the `B + 1`-atom moment budget, propagation gives a pointwise
bound; at or above a `B + 1` cluster budget, a propagating cluster spike remains possible. -/
theorem budgetedPropagationMomentGate
    [Nonempty α]
    {T A : ℝ} {k B : ℕ} (hT_nonneg : 0 ≤ T) (hk : 1 ≤ k) :
    ((Fintype.card α : ℝ) * A < ((B + 1 : ℕ) : ℝ) * T ^ k ->
        ∀ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ->
          powMomentAverage X k ≤ A ->
          ∀ R : α -> α -> Prop,
            BadPropagates R (scoreBad X T) (B + 1) ->
            ∀ a : α, X a < T)
      ∧
      (∀ (cluster : Finset α) (S : ℝ),
        cluster.card = B + 1 ->
        0 ≤ S -> 0 < T -> T ≤ S ->
        ((cluster.card : ℝ) * S ^ k) / (Fintype.card α : ℝ) ≤ A ->
        ∃ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ∧
          powMomentAverage X k ≤ A ∧
          B < weakTailCount X T ∧
          BadPropagates (clusterRelation cluster) (scoreBad X T) (B + 1)) := by
  constructor
  · intro hbudget X hX havg R hprop
    exact forall_lt_threshold_of_budgetedMoment_and_badPropagates
      (α := α) (X := X) (T := T) (A := A) (k := k) (B := B) (R := R)
      hX hT_nonneg havg hbudget hprop
  · intro cluster S hcard hS hTpos hTS hbudget
    exact averageMoment_budget_allows_propagating_cluster_spike
      (α := α) (T := T) (S := S) (A := A) (k := k) (B := B)
      hk hcard hS hTpos hTS hbudget

#print axioms badCount_scoreBad_eq_weakTailCount
#print axioms forall_lt_threshold_of_budgetedMoment_and_minimumTailCard
#print axioms forall_lt_threshold_of_budgetedMoment_and_badPropagates
#print axioms badNeighborhoodCount_clusterSpike_clusterRelation
#print axioms clusterSpike_badPropagates_clusterRelation
#print axioms averageMoment_budget_allows_propagating_cluster_spike
#print axioms budgetedPropagationMomentGate

end ArkLib.ProximityGap.Frontier.BudgetedPropagationMomentGate
