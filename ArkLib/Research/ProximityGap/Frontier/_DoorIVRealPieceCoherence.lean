/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV real-piece coherence constraint

A repeated failure mode in the localized door-(iv) probes is that a proposed split of the monomial
sum uses pieces that are already forced onto the real line.  If the adversarial frequency makes
those real pieces share one sign, the normalized coherence

`|Σ A_i| / Σ |A_i|`

is exactly `1`.  This file records the general finite-list version of that constraint.  It is not a
CORE bound: it says that real, same-sign piece decompositions have no anti-concentration slack.
-/

namespace ProximityGap.Frontier.DoorIVRealPieceCoherence

/-- Coherence of a finite list of real pieces. -/
noncomputable def realPieceCoherence (xs : List ℝ) : ℝ := |xs.sum| / (xs.map abs).sum

/-- For a nonnegative list, the sum of absolute values is the ordinary sum. -/
theorem sum_abs_eq_sum_of_forall_nonneg {xs : List ℝ}
    (h : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map abs).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : 0 ≤ a := h a (by simp)
      have hxs : ∀ x ∈ xs, 0 ≤ x := by
        intro x hx
        exact h x (by simp [hx])
      simp [abs_of_nonneg ha, ih hxs]

/-- For a nonpositive list, the sum of absolute values is the negated ordinary sum. -/
theorem sum_abs_eq_neg_sum_of_forall_nonpos {xs : List ℝ}
    (h : ∀ x ∈ xs, x ≤ 0) :
    (xs.map abs).sum = -xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : a ≤ 0 := h a (by simp)
      have hxs : ∀ x ∈ xs, x ≤ 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp [abs_of_nonpos ha, ih hxs]
      ring

/-- Any nonzero nonnegative real-piece split has coherence exactly one. -/
theorem realPieceCoherence_eq_one_of_forall_nonneg {xs : List ℝ}
    (h : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) :
    realPieceCoherence xs = 1 := by
  unfold realPieceCoherence
  rw [sum_abs_eq_sum_of_forall_nonneg h, abs_of_nonneg (le_of_lt hsum)]
  exact div_self (ne_of_gt hsum)

/-- Any nonzero nonpositive real-piece split has coherence exactly one. -/
theorem realPieceCoherence_eq_one_of_forall_nonpos {xs : List ℝ}
    (h : ∀ x ∈ xs, x ≤ 0) (hsum : xs.sum < 0) :
    realPieceCoherence xs = 1 := by
  unfold realPieceCoherence
  rw [sum_abs_eq_neg_sum_of_forall_nonpos h, abs_of_nonpos (le_of_lt hsum)]
  exact div_self (ne_of_gt (neg_pos.mpr hsum))

/-- The absolute-mass denominator is nonnegative (a sum of absolute values). -/
theorem sum_abs_nonneg (xs : List ℝ) : 0 ≤ (xs.map abs).sum := by
  apply List.sum_nonneg
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact abs_nonneg x

/-- The total signed sum never exceeds the absolute-mass denominator (triangle inequality for
lists).  This is the list-level `|∑ A_i| ≤ ∑ |A_i|` behind `realPieceCoherence ≤ 1`. -/
theorem abs_sum_le_sum_abs (xs : List ℝ) : |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.sum_cons, List.map_cons]
      calc |a + xs.sum| ≤ |a| + |xs.sum| := abs_add_le a xs.sum
        _ ≤ |a| + (xs.map abs).sum := by linarith

/-- Real-piece coherence is always at most `1` once the absolute mass is positive: the list-level
triangle inequality.  No real-piece split can exceed unit coherence. -/
theorem realPieceCoherence_le_one {xs : List ℝ} (hden : 0 < (xs.map abs).sum) :
    realPieceCoherence xs ≤ 1 := by
  unfold realPieceCoherence
  exact (div_le_one hden).mpr (abs_sum_le_sum_abs xs)

/-- **Strict real-piece slack forces a strictly negative piece.**  If a list with positive
signed sum has coherence strictly below `1`, it must contain a strictly negative element.  In
contrapositive: an all-nonnegative split (no negative piece) with positive sum has no slack
(coherence `1`).  So a real, positive-leaning Door-IV refinement cannot manufacture
anti-concentration without genuine negative mass. -/
theorem exists_neg_of_realPieceCoherence_lt_one_of_sum_pos {xs : List ℝ}
    (hsum : 0 < xs.sum) (hcoh : realPieceCoherence xs < 1) :
    ∃ x ∈ xs, x < 0 := by
  by_contra hno
  push_neg at hno
  have hnonneg : ∀ x ∈ xs, 0 ≤ x := fun x hx => hno x hx
  have heq := realPieceCoherence_eq_one_of_forall_nonneg hnonneg hsum
  rw [heq] at hcoh
  exact lt_irrefl _ hcoh

/-- **Strict real-piece slack forces a strictly positive piece** (the mirror case).  If a list
with negative signed sum has coherence strictly below `1`, it must contain a strictly positive
element.  An all-nonpositive split with negative sum has no slack. -/
theorem exists_pos_of_realPieceCoherence_lt_one_of_sum_neg {xs : List ℝ}
    (hsum : xs.sum < 0) (hcoh : realPieceCoherence xs < 1) :
    ∃ x ∈ xs, 0 < x := by
  by_contra hno
  push_neg at hno
  have hnonpos : ∀ x ∈ xs, x ≤ 0 := fun x hx => hno x hx
  have heq := realPieceCoherence_eq_one_of_forall_nonpos hnonpos hsum
  rw [heq] at hcoh
  exact lt_irrefl _ hcoh

/-- **Real-piece slack is exactly genuine sign mixing.**  For a list with nonzero signed sum,
coherence strictly below `1` forces BOTH a strictly positive and a strictly negative piece to be
present.  This is the list-level Door-IV constraint matching the compressed sign-mass criterion
`signMassCoherence_lt_one_iff_min_pos`: a real, negation-stable refinement only supplies
anti-concentration slack if it actually carries cancelling sign mass; merely renaming a finer
real decomposition does not. -/
theorem realPieceCoherence_lt_one_forces_both_signs {xs : List ℝ}
    (hsum : xs.sum ≠ 0) (hcoh : realPieceCoherence xs < 1) :
    (∃ x ∈ xs, 0 < x) ∧ (∃ x ∈ xs, x < 0) := by
  rcases lt_or_gt_of_ne hsum with hneg | hpos
  · -- xs.sum < 0 : a positive piece exists; a negative piece exists since the sum is negative.
    refine ⟨exists_pos_of_realPieceCoherence_lt_one_of_sum_neg hneg hcoh, ?_⟩
    by_contra hno
    push_neg at hno
    have hnonneg : ∀ x ∈ xs, 0 ≤ x := fun x hx => hno x hx
    have : 0 ≤ xs.sum := List.sum_nonneg hnonneg
    linarith
  · -- xs.sum > 0 : a negative piece exists; a positive piece exists since the sum is positive.
    refine ⟨?_, exists_neg_of_realPieceCoherence_lt_one_of_sum_pos hpos hcoh⟩
    by_contra hno
    push_neg at hno
    have hnonpos : ∀ x ∈ xs, x ≤ 0 := fun x hx => hno x hx
    have hneg_nonneg : 0 ≤ (xs.map Neg.neg).sum := by
      apply List.sum_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact neg_nonneg.mpr (hnonpos x hx)
    have hmapneg : ∀ l : List ℝ, (l.map Neg.neg).sum = -l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih =>
          simp only [List.map_cons, List.sum_cons, ih]
          ring
    rw [hmapneg xs] at hneg_nonneg
    have : xs.sum ≤ 0 := by linarith
    linarith

#print axioms sum_abs_eq_sum_of_forall_nonneg
#print axioms sum_abs_eq_neg_sum_of_forall_nonpos
#print axioms realPieceCoherence_eq_one_of_forall_nonneg
#print axioms realPieceCoherence_eq_one_of_forall_nonpos
#print axioms sum_abs_nonneg
#print axioms abs_sum_le_sum_abs
#print axioms realPieceCoherence_le_one
#print axioms exists_neg_of_realPieceCoherence_lt_one_of_sum_pos
#print axioms exists_pos_of_realPieceCoherence_lt_one_of_sum_neg
#print axioms realPieceCoherence_lt_one_forces_both_signs

end ProximityGap.Frontier.DoorIVRealPieceCoherence
