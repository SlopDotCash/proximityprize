/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Vertical tail bounds consume only at atom scale

The distributional face of issue #464 asks for an effective tail bound for the Gauss-period values
indexed by the dilation quotient.  This file records the exact finite consumer:

* a tail bound below the mass of one atom gives the desired pointwise/sup bound;
* any tail bound at or above one atom is compatible with a single spike above threshold.

Thus a vertical Sato--Tate, Wasserstein, discrepancy, or empirical-tail theorem is prize-facing only
if its upper tail at the prize threshold is below `1 / #atoms`.  Otherwise one bad frequency can
survive the distributional estimate.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer

variable {α : Type} [Fintype α]

/-- Number of atoms with score strictly above threshold `T`. -/
noncomputable def tailCount (X : α -> ℝ) (T : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a => T < X a)).card

/-- Uniform empirical mass of the strict upper tail above threshold `T`. -/
noncomputable def tailMass (X : α -> ℝ) (T : ℝ) : ℝ :=
  (tailCount X T : ℝ) / (Fintype.card α : ℝ)

/-- The strict upper tail is empty exactly when every score is at most the threshold. -/
theorem tailCount_eq_zero_iff_forall_le (X : α -> ℝ) (T : ℝ) :
    tailCount X T = 0 ↔ ∀ a : α, X a ≤ T := by
  classical
  unfold tailCount
  rw [Finset.card_eq_zero]
  constructor
  · intro hempty a
    exact le_of_not_gt (fun hgt => by
      have hmem : a ∈ (Finset.univ.filter (fun a => T < X a)) := by
        simp [hgt]
      rw [hempty] at hmem
      simpa using hmem)
  · intro hle
    ext a
    simp [not_lt.mpr (hle a)]

/-- If some atom is above threshold, the strict upper tail has count at least one. -/
theorem one_le_tailCount_of_exists_gt
    {X : α -> ℝ} {T : ℝ} (hgt : ∃ a : α, T < X a) :
    1 ≤ tailCount X T := by
  classical
  rcases hgt with ⟨a, ha⟩
  unfold tailCount
  exact Finset.one_le_card.mpr ⟨a, by simp [ha]⟩

/-- If some atom is above threshold, the strict upper-tail mass is at least one atom. -/
theorem inv_card_le_tailMass_of_exists_gt
    {X : α -> ℝ} {T : ℝ} (hgt : ∃ a : α, T < X a) :
    (1 : ℝ) / (Fintype.card α : ℝ) ≤ tailMass X T := by
  classical
  rcases hgt with ⟨a, ha⟩
  have hden_nonneg : (0 : ℝ) ≤ (Fintype.card α : ℝ) := by positivity
  have hcount : (1 : ℝ) ≤ (tailCount X T : ℝ) := by
    exact_mod_cast (one_le_tailCount_of_exists_gt (X := X) (T := T) ⟨a, ha⟩)
  unfold tailMass
  exact div_le_div_of_nonneg_right hcount hden_nonneg

/-- A tail-mass estimate below one atom gives the pointwise/sup bound `X a <= T`. -/
theorem forall_le_of_tailMass_lt_inv_card
    {X : α -> ℝ} {T : ℝ}
    (hsmall : tailMass X T < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, X a ≤ T := by
  classical
  intro a
  exact le_of_not_gt (fun hgt =>
    (not_lt_of_ge (inv_card_le_tailMass_of_exists_gt (X := X) (T := T) ⟨a, hgt⟩)) hsmall)

/-- A distributional tail upper bound below one atom is enough for a pointwise/sup bound. -/
theorem forall_le_of_tailMass_bound_lt_inv_card
    {X : α -> ℝ} {T U : ℝ}
    (hmass : tailMass X T ≤ U)
    (hU : U < (1 : ℝ) / (Fintype.card α : ℝ)) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_tailMass_lt_inv_card (X := X) (T := T) (lt_of_le_of_lt hmass hU)

/-- A singleton score spike above threshold has tail mass exactly one atom. -/
theorem tailMass_single_spike [DecidableEq α] (a₀ : α) (T : ℝ) :
    tailMass (fun a : α => if a = a₀ then T + 1 else T) T
      = (1 : ℝ) / (Fintype.card α : ℝ) := by
  classical
  have hfilter :
      (Finset.univ.filter (fun a : α => T < if a = a₀ then T + 1 else T))
        = ({a₀} : Finset α) := by
    ext a
    by_cases ha : a = a₀
    · simp [ha]
    · simp [ha]
  unfold tailMass tailCount
  rw [hfilter]
  simp

/-- Any tail-mass budget at least one atom is compatible with one score above threshold. -/
theorem tailMass_budget_allows_single_score_spike [Nonempty α] [DecidableEq α]
    {T U : ℝ}
    (hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U) :
    ∃ X : α -> ℝ, tailMass X T ≤ U ∧ ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨fun a : α => if a = a₀ then T + 1 else T, ?_, ⟨a₀, by simp⟩⟩
  simpa [tailMass_single_spike] using hU

/-- Exact atom-scale gate for turning a distributional upper-tail theorem into a pointwise/sup
theorem at threshold `T`. -/
theorem atomScaleGate_for_tailSupBound [Nonempty α] [DecidableEq α] {T U : ℝ} :
    (∀ X : α -> ℝ, tailMass X T ≤ U -> ∀ a : α, X a ≤ T)
      ↔ U < (1 : ℝ) / (Fintype.card α : ℝ) := by
  constructor
  · intro h
    by_contra hnot
    have hU : (1 : ℝ) / (Fintype.card α : ℝ) ≤ U := le_of_not_gt hnot
    rcases tailMass_budget_allows_single_score_spike (α := α) (T := T) hU with
      ⟨X, hmass, a, hgt⟩
    exact (not_lt_of_ge (h X hmass a)) hgt
  · intro hU X hmass
    exact forall_le_of_tailMass_bound_lt_inv_card (X := X) (T := T) hmass hU

end ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.tailCount_eq_zero_iff_forall_le
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.one_le_tailCount_of_exists_gt
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.inv_card_le_tailMass_of_exists_gt
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.forall_le_of_tailMass_lt_inv_card
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.forall_le_of_tailMass_bound_lt_inv_card
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.tailMass_single_spike
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.tailMass_budget_allows_single_score_spike
#print axioms ArkLib.ProximityGap.Frontier.VerticalTailSupConsumer.atomScaleGate_for_tailSupBound
