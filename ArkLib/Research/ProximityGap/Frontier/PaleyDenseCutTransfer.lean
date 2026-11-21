/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyBipartiteCrossRatio

/-!
# Transferring dense rectangle estimates through vertex signs

A ternary weight on a finite template can be tested using at most three
indicators of subsets of at least half the full size. This applies uniformly
to incomplete supports and to the signs attached by a projective chart.
-/

namespace ProximityGap.PaleyDenseCutTransfer

open Finset PaleyBipartiteCrossRatio

variable {α β : Type*}

/-- A bound on all half-size-or-larger sets controls all ternary weighted sums. -/
theorem ternary_sum (S : Finset α) (u f : α → ℤ) (H : ℤ)
    (hu : ∀ x ∈ S, |u x| ≤ 1)
    (hS : ∀ U ⊆ S, S.card ≤ 2*U.card → |∑ x ∈ U, f x| ≤ H) :
    |∑ x ∈ S, u x * f x| ≤ 3*H := by
  classical
  let P := S.filter (fun x => u x = 1)
  let N := S.filter (fun x => u x = -1)
  have hc (U : Finset α) (hU : U ⊆ S) :
      (-H ≤ (∑ x ∈ U, f x) ∧ (∑ x ∈ U, f x) ≤ H) ∨
      (-H ≤ (∑ x ∈ S, f x) - ∑ x ∈ U, f x ∧ (∑ x ∈ S, f x) - ∑ x ∈ U, f x ≤ H) := by
    by_cases h : S.card ≤ 2*U.card
    · exact Or.inl (abs_le.mp (hS U hU h))
    · have h' : S.card ≤ 2*(S\U).card := by rw [card_sdiff_of_subset hU]; omega
      have hc := abs_le.mp (hS (S\U) sdiff_subset h')
      have hd := Finset.sum_sdiff hU (f := f)
      right
      omega
  have hp := hc P (filter_subset ..)
  have hn := hc N (filter_subset ..)
  have hs := abs_le.mp (hS S (Subset.rfl) (by omega))
  have split : ∑ x ∈ S, u x * f x = (∑ x ∈ P, f x) - ∑ x ∈ N, f x := by
    simp only [P, N, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hz := abs_le.mp (hu x hx)
    have : u x = 0 ∨ u x = 1 ∨ u x = -1 := by omega
    rcases this with h|h|h <;> simp [h]
  rw [split, abs_le]
  rcases hp with hp|hp <;> rcases hn with hn|hn <;> omega

/-- Dense unweighted estimates suffice for arbitrary ternary weights on both templates. -/
theorem weighted_rectangle (A : Finset α) (B : Finset β) (W : α → β → ℤ)
    (u : α → ℤ) (v : β → ℤ) (H : ℤ)
    (hu : ∀ x ∈ A, |u x| ≤ 1) (hv : ∀ b ∈ B, |v b| ≤ 1)
    (hcut : ∀ U ⊆ A, A.card ≤ 2*U.card → ∀ V ⊆ B, B.card ≤ 2*V.card →
      |∑ x ∈ U, ∑ b ∈ V, W x b| ≤ H) :
    |∑ x ∈ A, u x * ∑ b ∈ B, v b * W x b| ≤ 9*H := by
  rw [show 9*H=3*(3*H) by ring]
  apply ternary_sum A u _ (3*H) hu
  intro U hU hsize
  rw [Finset.sum_comm]
  simp_rw [← mul_sum]
  apply ternary_sum B v _ H hv
  intro V hV hsize'
  rw [Finset.sum_comm]
  exact hcut U hU hsize V hV hsize'

/-- Bounds for dense unweighted cuts control four-cycle energy with a constant loss. -/
theorem energy_le_dense_cuts (A : Finset α) (B : Finset β) (W : α → β → ℤ) (H : ℤ)
    (hw : ∀ x ∈ A, ∀ b ∈ B, |W x b| ≤ 1)
    (hcut : ∀ U ⊆ A, A.card ≤ 2*U.card → ∀ V ⊆ B, B.card ≤ 2*V.card →
      |∑ x ∈ U, ∑ b ∈ V, W x b| ≤ H) :
    energy A B W ≤ 9*H*A.card*B.card := by
  have hanchor (t : β) (ht : t ∈ B) (y : α) (hy : y ∈ A) :
      W y t * (∑ x ∈ A, W x t * ∑ b ∈ B, W y b * W x b) ≤ 9*H := by
    have h := weighted_rectangle A B W (fun x => W x t) (W y) H
      (fun x hx => hw x hx t ht) (hw y hy) hcut
    calc
      _ ≤ |W y t| * |∑ x ∈ A, W x t * ∑ b ∈ B, W y b * W x b| := by
        rw [← abs_mul]; exact le_abs_self _
      _ ≤ 1 * |∑ x ∈ A, W x t * ∑ b ∈ B, W y b * W x b| :=
        mul_le_mul_of_nonneg_right (hw y hy t ht) (abs_nonneg _)
      _ ≤ _ := by simpa using h
  calc
    _ = ∑ t ∈ B, ∑ y ∈ A, W y t * ∑ x ∈ A, W x t * ∑ b ∈ B, W y b * W x b := by
      rw [energy_eq_four_cycle]
      simp_rw [mul_sum]
      refine sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro y _
      exact sum_congr rfl fun b _ => by ring
    _ ≤ ∑ _t ∈ B, ∑ _y ∈ A, 9*H := sum_le_sum fun t ht => sum_le_sum (hanchor t ht)
    _ = _ := by simp [mul_comm]

end ProximityGap.PaleyDenseCutTransfer

#print axioms ProximityGap.PaleyDenseCutTransfer.weighted_rectangle
#print axioms ProximityGap.PaleyDenseCutTransfer.energy_le_dense_cuts
