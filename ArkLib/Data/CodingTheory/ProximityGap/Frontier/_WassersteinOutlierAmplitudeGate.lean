/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Wasserstein outlier amplitude gate

`_WassersteinAtomScaleBarrier` and `_WassersteinSmoothingAtomGate` record the tail-mass version of
the issue #464 obstruction: a distributional theorem becomes pointwise only below one-atom mass.

This file records the complementary amplitude obstruction.  A `W₁`-type average transport bound can
hide one outlier whose height is the atom count times the average budget.  Therefore a Wasserstein
or effective-equidistribution theorem alone gives a supremum bound at threshold `T` only when

`#atoms * W < T`.

At the opposite scale, a one-outlier model has average transport `H / #atoms` and supremum `H`.  The
gate is purely finite and makes no claim about Gauss periods; it isolates the extra rate any
KU/Katz/Wasserstein route would need before it can imply the Paley/far-line worst-case bound.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.WassersteinOutlierAmplitudeGate

variable {α : Type} [Fintype α]

/-- A finite `W₁`-style cost to the zero profile for nonnegative scalar scores. -/
noncomputable def meanTransportToZero (X : α -> ℝ) : ℝ :=
  (∑ a : α, X a) / (Fintype.card α : ℝ)

/-- A single nonnegative score is at most the unnormalized transport sum. -/
theorem single_le_transportSum
    {X : α -> ℝ} (hX : ∀ a : α, 0 ≤ X a) (a₀ : α) :
    X a₀ ≤ ∑ a : α, X a := by
  exact single_le_sum (fun a _ha => hX a) (mem_univ a₀)

/-- An average transport bound gives the corresponding unnormalized transport bound. -/
theorem transportSum_le_card_mul_of_meanTransport_le [Nonempty α]
    {X : α -> ℝ} {W : ℝ}
    (hW : meanTransportToZero X ≤ W) :
    (∑ a : α, X a) ≤ (Fintype.card α : ℝ) * W := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  unfold meanTransportToZero at hW
  have h := (div_le_iff₀ hcard_pos).mp hW
  simpa [mul_comm] using h

/-- Operational consumer: an average `W₁` cost proves `X a < T` for every atom only when the
total possible one-outlier amplitude `#α * W` is strictly below `T`. -/
theorem forall_lt_of_meanTransport_card_mul_lt [Nonempty α]
    {X : α -> ℝ} {W T : ℝ}
    (hX : ∀ a : α, 0 ≤ X a)
    (hmean : meanTransportToZero X ≤ W)
    (hbudget : (Fintype.card α : ℝ) * W < T) :
    ∀ a : α, X a < T := by
  intro a
  exact lt_of_le_of_lt
    (le_trans (single_le_transportSum hX a)
      (transportSum_le_card_mul_of_meanTransport_le (α := α) hmean))
    hbudget

/-- The one-outlier score profile. -/
def oneOutlier [DecidableEq α] (a₀ : α) (H : ℝ) : α -> ℝ :=
  fun a : α => if a = a₀ then H else 0

/-- The transport sum of a one-outlier profile is exactly the outlier height. -/
theorem transportSum_oneOutlier [DecidableEq α] (a₀ : α) (H : ℝ) :
    (∑ a : α, oneOutlier a₀ H a) = H := by
  classical
  simp [oneOutlier]

/-- The mean transport of a one-outlier profile is exactly `H / #α`. -/
theorem meanTransport_oneOutlier [DecidableEq α] (a₀ : α) (H : ℝ) :
    meanTransportToZero (oneOutlier a₀ H) = H / (Fintype.card α : ℝ) := by
  simp [meanTransportToZero, transportSum_oneOutlier]

omit [Fintype α] in
/-- A nonnegative outlier profile is entrywise nonnegative. -/
theorem oneOutlier_nonneg [DecidableEq α] {a₀ : α} {H : ℝ} (hH : 0 ≤ H) :
    ∀ a : α, 0 ≤ oneOutlier a₀ H a := by
  intro a
  by_cases h : a = a₀
  · simp [oneOutlier, h, hH]
  · simp [oneOutlier, h]

/-- If the average transport budget can pay for one outlier of height `H > T`, then the budget is
compatible with a score above the threshold. -/
theorem meanTransport_budget_allows_oneOutlier
    [Nonempty α]
    {W T H : ℝ}
    (hH_nonneg : 0 ≤ H)
    (hTH : T < H)
    (hbudget : H / (Fintype.card α : ℝ) ≤ W) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      meanTransportToZero X ≤ W ∧
      ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨oneOutlier a₀ H, oneOutlier_nonneg hH_nonneg, ?_, ⟨a₀, ?_⟩⟩
  · simpa [meanTransport_oneOutlier] using hbudget
  · simpa [oneOutlier] using hTH

/-- Rate form of the obstruction: if `H <= #α * W`, a one-outlier profile of height `H` fits
inside the average transport budget. -/
theorem meanTransport_budget_allows_oneOutlier_of_height_le_card_mul
    [Nonempty α]
    {W T H : ℝ}
    (hH_nonneg : 0 ≤ H)
    (hTH : T < H)
    (hbudget : H ≤ (Fintype.card α : ℝ) * W) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      meanTransportToZero X ≤ W ∧
      ∃ a : α, T < X a := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  have hdiv : H / (Fintype.card α : ℝ) ≤ W := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using hbudget
  exact meanTransport_budget_allows_oneOutlier
    (α := α) hH_nonneg hTH hdiv

/-- Two-sided finite gate for converting a `W₁`-style average transport estimate into a supremum
bound.  The consumer needs `#α * W < T`; the obstruction shows one outlier survives whenever the
budget can pay for a height `H > T`. -/
theorem wassersteinOutlierAmplitudeGate [Nonempty α]
    {W T : ℝ} :
    ((Fintype.card α : ℝ) * W < T ->
        ∀ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ->
          meanTransportToZero X ≤ W ->
          ∀ a : α, X a < T)
      ∧
      (∀ H : ℝ, 0 ≤ H -> T < H -> H ≤ (Fintype.card α : ℝ) * W ->
        ∃ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ∧
          meanTransportToZero X ≤ W ∧
          ∃ a : α, T < X a) := by
  constructor
  · intro hbudget X hX hmean
    exact forall_lt_of_meanTransport_card_mul_lt hX hmean hbudget
  · intro H hH hTH hbudget
    exact meanTransport_budget_allows_oneOutlier_of_height_le_card_mul
      (α := α) hH hTH hbudget

#print axioms single_le_transportSum
#print axioms transportSum_le_card_mul_of_meanTransport_le
#print axioms forall_lt_of_meanTransport_card_mul_lt
#print axioms transportSum_oneOutlier
#print axioms meanTransport_oneOutlier
#print axioms oneOutlier_nonneg
#print axioms meanTransport_budget_allows_oneOutlier
#print axioms meanTransport_budget_allows_oneOutlier_of_height_le_card_mul
#print axioms wassersteinOutlierAmplitudeGate

end ArkLib.ProximityGap.Frontier.WassersteinOutlierAmplitudeGate
