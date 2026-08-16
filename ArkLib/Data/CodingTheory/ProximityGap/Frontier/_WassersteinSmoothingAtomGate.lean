/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._VerticalTailSupConsumer
import Mathlib.Tactic

/-!
# Wasserstein smoothing still has an atom-scale gate

The usual way to turn a Wasserstein or discrepancy estimate into a tail estimate is to replace the
hard indicator `1_{T < x}` by a soft test.  If the test majorizes the hard tail, then its empirical
average controls the tail mass.  A Wasserstein bound then contributes an error of the form `W / eta`
for a ramp of width `eta`.

This file records the finite last-mile gate.  A smoothed certificate with budget `B` proves the
pointwise bound only when `B < 1 / #α`, equivalently `#α * B < 1`.  At or above one-atom scale a
single spike is compatible with the same style of smoothed certificate.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.WassersteinSmoothingAtomGate

open ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer

variable {α : Type} [Fintype α]

/-- Uniform empirical average of a real soft test applied to the score function `X`. -/
noncomputable def softEmpiricalAverage (X : α -> ℝ) (φ : ℝ -> ℝ) : ℝ :=
  (∑ a : α, φ (X a)) / (Fintype.card α : ℝ)

/-- If a nonnegative soft test majorizes the hard upper-tail indicator, its empirical average
dominates the hard tail mass. -/
theorem tailMass_le_softEmpiricalAverage_of_majorizes_tail
    {X : α -> ℝ} {φ : ℝ -> ℝ} {T : ℝ}
    (hφ_nonneg : ∀ a : α, 0 ≤ φ (X a))
    (hmajor : ∀ a : α, T < X a -> 1 ≤ φ (X a)) :
    tailMass X T ≤ softEmpiricalAverage X φ := by
  classical
  have hcount_sum :
      ((tailCount X T : ℕ) : ℝ)
        = ∑ a : α, if T < X a then (1 : ℝ) else 0 := by
    unfold tailCount
    simp
  have hsum_le :
      (∑ a : α, if T < X a then (1 : ℝ) else 0)
        ≤ ∑ a : α, φ (X a) := by
    refine Finset.sum_le_sum ?_
    intro a _ha
    by_cases hgt : T < X a
    · simpa [hgt] using hmajor a hgt
    · simpa [hgt] using hφ_nonneg a
  unfold tailMass softEmpiricalAverage
  rw [hcount_sum]
  exact div_le_div_of_nonneg_right hsum_le (by positivity)

/-- A soft-test budget below one atom gives the pointwise upper bound. -/
theorem forall_le_of_softEmpiricalAverage_bound_lt_inv_card
    {X : α -> ℝ} {φ : ℝ -> ℝ} {T B : ℝ}
    (hφ_nonneg : ∀ a : α, 0 ≤ φ (X a))
    (hmajor : ∀ a : α, T < X a -> 1 ≤ φ (X a))
    (hsoft : softEmpiricalAverage X φ ≤ B)
    (hB : B < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_tailMass_bound_lt_inv_card
    (X := X) (T := T) (U := B)
    (le_trans (tailMass_le_softEmpiricalAverage_of_majorizes_tail hφ_nonneg hmajor) hsoft) hB

/-- Rate form: `#α * B < 1` is equivalent to the soft budget being below one atom. -/
theorem softBudget_lt_inv_card_of_card_mul_lt_one [Nonempty α]
    {B : ℝ}
    (hcardB : (Fintype.card α : ℝ) * B < 1) :
    B < (1 : ℝ) / (Fintype.card α : ℝ) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  have hdiv := div_lt_div_of_pos_right hcardB hcard_pos
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hleft : ((Fintype.card α : ℝ) * B) / (Fintype.card α : ℝ) = B := by
    field_simp [hcard_ne]
  rwa [hleft] at hdiv

/-- Operational smoothed-tail consumer.  A soft-test budget `B` proves the hard pointwise bound once
the total atom budget `#α * B` is strictly below one. -/
theorem forall_le_of_softEmpiricalAverage_bound_card_mul_lt_one [Nonempty α]
    {X : α -> ℝ} {φ : ℝ -> ℝ} {T B : ℝ}
    (hφ_nonneg : ∀ a : α, 0 ≤ φ (X a))
    (hmajor : ∀ a : α, T < X a -> 1 ≤ φ (X a))
    (hsoft : softEmpiricalAverage X φ ≤ B)
    (hcardB : (Fintype.card α : ℝ) * B < 1) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_softEmpiricalAverage_bound_lt_inv_card hφ_nonneg hmajor hsoft
    (softBudget_lt_inv_card_of_card_mul_lt_one (α := α) hcardB)

/-- Wasserstein-style smoothing consumer.  If a ramp of width `eta` gives a certificate
`targetTail + transport / eta`, then this proves the hard threshold `T + eta` only after that
quantity beats one atom. -/
theorem forall_le_threshold_plus_margin_of_wassersteinSmoothBudget [Nonempty α]
    {X : α -> ℝ} {φ : ℝ -> ℝ} {T targetTail transport eta : ℝ}
    (hφ_nonneg : ∀ a : α, 0 ≤ φ (X a))
    (hmajor : ∀ a : α, T + eta < X a -> 1 ≤ φ (X a))
    (hsoft : softEmpiricalAverage X φ ≤ targetTail + transport / eta)
    (hbudget : (Fintype.card α : ℝ) * (targetTail + transport / eta) < 1) :
    ∀ a : α, X a ≤ T + eta :=
  forall_le_of_softEmpiricalAverage_bound_card_mul_lt_one
    (α := α) (X := X) (φ := φ) (T := T + eta) (B := targetTail + transport / eta)
    hφ_nonneg hmajor hsoft hbudget

/-- The hard cutoff applied to a single score spike has soft average exactly one atom. -/
theorem softEmpiricalAverage_single_spike_cutoff [DecidableEq α] (a₀ : α) (T : ℝ) :
    softEmpiricalAverage
        (fun a : α => if a = a₀ then T + 1 else T)
        (fun x : ℝ => if T < x then (1 : ℝ) else 0)
      = (1 : ℝ) / (Fintype.card α : ℝ) := by
  classical
  unfold softEmpiricalAverage
  have hsum :
      (∑ a : α,
          (if T < (if a = a₀ then T + 1 else T) then (1 : ℝ) else 0))
        = 1 := by
    calc
      (∑ a : α,
          (if T < (if a = a₀ then T + 1 else T) then (1 : ℝ) else 0))
          = ∑ a : α, if a = a₀ then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            by_cases ha : a = a₀
            · have hlt : T < T + 1 := by linarith
              simp [ha, hlt]
            · simp [ha]
      _ = 1 := by simp
  rw [hsum]

/-- Any soft budget at least one atom is compatible with one score above threshold. -/
theorem softBudget_allows_single_spike [Nonempty α] [DecidableEq α]
    {T B : ℝ}
    (hB : (1 : ℝ) / (Fintype.card α : ℝ) ≤ B) :
    ∃ X : α -> ℝ, ∃ φ : ℝ -> ℝ,
      (∀ a : α, 0 ≤ φ (X a)) ∧
      (∀ a : α, T < X a -> 1 ≤ φ (X a)) ∧
      softEmpiricalAverage X φ ≤ B ∧
      ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine
    ⟨fun a : α => if a = a₀ then T + 1 else T,
      fun x : ℝ => if T < x then (1 : ℝ) else 0, ?_, ?_, ?_, ⟨a₀, ?_⟩⟩
  · intro a
    by_cases hgt : T < (if a = a₀ then T + 1 else T)
    · simp [hgt]
    · simp [hgt]
  · intro a hgt
    simp [hgt]
  · simpa [softEmpiricalAverage_single_spike_cutoff a₀ T] using hB
  · simp

/-- Rate form of the one-atom obstruction for soft-test certificates. -/
theorem softBudget_allows_single_spike_of_one_le_card_mul
    [Nonempty α] [DecidableEq α]
    {T B : ℝ}
    (hcardB : 1 ≤ (Fintype.card α : ℝ) * B) :
    ∃ X : α -> ℝ, ∃ φ : ℝ -> ℝ,
      (∀ a : α, 0 ≤ φ (X a)) ∧
      (∀ a : α, T < X a -> 1 ≤ φ (X a)) ∧
      softEmpiricalAverage X φ ≤ B ∧
      ∃ a : α, T < X a := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  have hdiv := div_le_div_of_nonneg_right hcardB (le_of_lt hcard_pos)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hright : ((Fintype.card α : ℝ) * B) / (Fintype.card α : ℝ) = B := by
    field_simp [hcard_ne]
  have hB : (1 : ℝ) / (Fintype.card α : ℝ) ≤ B := by
    rwa [hright] at hdiv
  exact softBudget_allows_single_spike (α := α) (T := T) hB

/-- Exact atom-scale gate for soft smoothed-tail certificates. -/
theorem atomScaleGate_for_smoothedTailCertificate [Nonempty α] [DecidableEq α]
    {T B : ℝ} :
    (∀ X : α -> ℝ, ∀ φ : ℝ -> ℝ,
        (∀ a : α, 0 ≤ φ (X a)) ->
        (∀ a : α, T < X a -> 1 ≤ φ (X a)) ->
        softEmpiricalAverage X φ ≤ B ->
        ∀ a : α, X a ≤ T)
      ↔ B < (1 : ℝ) / (Fintype.card α : ℝ) := by
  constructor
  · intro h
    by_contra hnot
    have hB : (1 : ℝ) / (Fintype.card α : ℝ) ≤ B := le_of_not_gt hnot
    rcases softBudget_allows_single_spike (α := α) (T := T) hB with
      ⟨X, φ, hφ_nonneg, hmajor, hsoft, a, hgt⟩
    exact (not_lt_of_ge (h X φ hφ_nonneg hmajor hsoft a)) hgt
  · intro hB X φ hφ_nonneg hmajor hsoft
    exact forall_le_of_softEmpiricalAverage_bound_lt_inv_card hφ_nonneg hmajor hsoft hB

#print axioms softEmpiricalAverage
#print axioms tailMass_le_softEmpiricalAverage_of_majorizes_tail
#print axioms forall_le_of_softEmpiricalAverage_bound_lt_inv_card
#print axioms softBudget_lt_inv_card_of_card_mul_lt_one
#print axioms forall_le_of_softEmpiricalAverage_bound_card_mul_lt_one
#print axioms forall_le_threshold_plus_margin_of_wassersteinSmoothBudget
#print axioms softEmpiricalAverage_single_spike_cutoff
#print axioms softBudget_allows_single_spike
#print axioms softBudget_allows_single_spike_of_one_le_card_mul
#print axioms atomScaleGate_for_smoothedTailCertificate

end ArkLib.ProximityGap.Frontier.WassersteinSmoothingAtomGate
