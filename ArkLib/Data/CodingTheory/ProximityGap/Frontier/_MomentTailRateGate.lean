/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Moment tail rate gate

The moment route to the issue #464 floor has two separate components:

* prove a high-moment / Wick-type estimate for the prize period family;
* consume that estimate as a worst-case supremum bound.

This file records the finite last-mile gate in a form that is insensitive to the surrounding
number theory.  For nonnegative scores on `N` atoms, an average `k`-th moment budget `A` proves
`X a <= T` for every atom once

`N * A <= T^k`.

Conversely, if a proposed average-moment budget is large enough to pay for one atom at score `S>T`,
then a one-spike score vector satisfies the moment budget while violating the desired supremum
bound.  Thus high moments become a worst-case floor proof only at the rate where Markov plus the
finite atom count beats one possible bad atom.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Frontier.MomentTailRateGate

variable {α : Type} [Fintype α]

/-- Unnormalized finite `k`-th power moment of a score function. -/
noncomputable def powMomentSum (X : α -> ℝ) (k : ℕ) : ℝ :=
  ∑ a : α, X a ^ k

/-- Uniform empirical average of the `k`-th power moment. -/
noncomputable def powMomentAverage (X : α -> ℝ) (k : ℕ) : ℝ :=
  powMomentSum X k / (Fintype.card α : ℝ)

/-- An average moment bound gives the corresponding unnormalized moment bound after multiplying by
the number of atoms. -/
theorem powMomentSum_le_card_mul_of_average_le [Nonempty α]
    {X : α -> ℝ} {k : ℕ} {A : ℝ}
    (havg : powMomentAverage X k ≤ A) :
    powMomentSum X k ≤ (Fintype.card α : ℝ) * A := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  unfold powMomentAverage at havg
  have h := (div_le_iff₀ hcard_pos).mp havg
  simpa [mul_comm] using h

/-- One term of a nonnegative finite moment sum is bounded by the whole moment sum. -/
theorem single_pow_le_powMomentSum
    {X : α -> ℝ} (hX : ∀ a : α, 0 ≤ X a) (k : ℕ) (a₀ : α) :
    X a₀ ^ k ≤ powMomentSum X k := by
  classical
  unfold powMomentSum
  exact single_le_sum (fun a _ => pow_nonneg (hX a) k) (mem_univ a₀)

/-- If the unnormalized moment is at most `T^k`, then no nonnegative score can exceed `T`. -/
theorem forall_le_of_powMomentSum_le_threshold
    {X : α -> ℝ} {T : ℝ} {k : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T) (hk : 1 ≤ k)
    (hsum : powMomentSum X k ≤ T ^ k) :
    ∀ a : α, X a ≤ T := by
  intro a
  by_contra hnot
  have hgt : T < X a := lt_of_not_ge hnot
  have hk0 : k ≠ 0 := by omega
  have hterm : T ^ k < X a ^ k := pow_lt_pow_left₀ hgt hT hk0
  have hle_sum : X a ^ k ≤ powMomentSum X k :=
    single_pow_le_powMomentSum hX k a
  exact (not_lt_of_ge hsum) (lt_of_lt_of_le hterm hle_sum)

/-- Average-moment rate gate: `#α * A <= T^k` turns an average `k`-th moment budget into a hard
supremum bound. -/
theorem forall_le_of_averageMoment_card_mul_le_threshold [Nonempty α]
    {X : α -> ℝ} {T A : ℝ} {k : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T) (hk : 1 ≤ k)
    (havg : powMomentAverage X k ≤ A)
    (hrate : (Fintype.card α : ℝ) * A ≤ T ^ k) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_powMomentSum_le_threshold hX hT hk
    (le_trans (powMomentSum_le_card_mul_of_average_le (α := α) havg) hrate)

/-- Strict operational form: `#α * A < T^k` is more than enough for the same hard supremum bound. -/
theorem forall_le_of_averageMoment_card_mul_lt_threshold [Nonempty α]
    {X : α -> ℝ} {T A : ℝ} {k : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T) (hk : 1 ≤ k)
    (havg : powMomentAverage X k ≤ A)
    (hrate : (Fintype.card α : ℝ) * A < T ^ k) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_averageMoment_card_mul_le_threshold
    hX hT hk havg (le_of_lt hrate)

/-- The score vector with one atom at `S` and all other atoms at zero has moment sum `S^k`. -/
theorem powMomentSum_single_spike [DecidableEq α]
    (a₀ : α) (S : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    powMomentSum (fun a : α => if a = a₀ then S else 0) k = S ^ k := by
  classical
  unfold powMomentSum
  calc
    (∑ a : α, (if a = a₀ then S else 0) ^ k)
        = ∑ a : α, (if a = a₀ then S ^ k else 0) := by
          refine sum_congr rfl ?_
          intro a _ha
          by_cases h : a = a₀
          · simp [h]
          · have hk0 : k ≠ 0 := by omega
            simp [h, hk0]
    _ = S ^ k := by simp

/-- The one-spike vector has average moment `S^k / #α`. -/
theorem powMomentAverage_single_spike [DecidableEq α]
    (a₀ : α) (S : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    powMomentAverage (fun a : α => if a = a₀ then S else 0) k
      = S ^ k / (Fintype.card α : ℝ) := by
  simp [powMomentAverage, powMomentSum_single_spike a₀ S hk]

/-- If the average-moment budget can pay for one atom at score `S > T`, a violating one-spike
score vector is compatible with the budget. -/
theorem averageMoment_budget_allows_single_spike [Nonempty α] [DecidableEq α]
    {T S A : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hS : 0 ≤ S) (hTS : T < S)
    (hbudget : S ^ k / (Fintype.card α : ℝ) ≤ A) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X k ≤ A ∧
      ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  refine ⟨fun a : α => if a = a₀ then S else 0, ?_, ?_, ⟨a₀, ?_⟩⟩
  · intro a
    by_cases h : a = a₀
    · simp [h, hS]
    · simp [h]
  · simpa [powMomentAverage_single_spike a₀ S hk] using hbudget
  · simp [hTS]

/-- Rate form of the one-spike obstruction: if `S^k <= #α * A`, the average moment budget admits a
single atom above threshold `T`, provided `S > T`. -/
theorem averageMoment_budget_allows_single_spike_of_pow_le_card_mul
    [Nonempty α] [DecidableEq α]
    {T S A : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hS : 0 ≤ S) (hTS : T < S)
    (hbudget : S ^ k ≤ (Fintype.card α : ℝ) * A) :
    ∃ X : α -> ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X k ≤ A ∧
      ∃ a : α, T < X a := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty α))
  have hdiv : S ^ k / (Fintype.card α : ℝ) ≤ A := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using hbudget
  exact averageMoment_budget_allows_single_spike (α := α) hk hS hTS hdiv

/-- Two-sided finite rate summary.  The first component is the consumer: a moment budget proves a
hard sup only when the atom-count rate beats `T^k`.  The second component is the obstruction:
whenever the same budget can pay for one atom at a larger score `S`, a one-spike countermodel
survives. -/
theorem momentTailRateGate [Nonempty α] [DecidableEq α]
    {T A : ℝ} {k : ℕ} (hT : 0 ≤ T) (hk : 1 ≤ k) :
    ((Fintype.card α : ℝ) * A ≤ T ^ k ->
        ∀ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ->
          powMomentAverage X k ≤ A ->
          ∀ a : α, X a ≤ T)
      ∧
      (∀ S : ℝ, 0 ≤ S -> T < S -> S ^ k ≤ (Fintype.card α : ℝ) * A ->
        ∃ X : α -> ℝ,
          (∀ a : α, 0 ≤ X a) ∧
          powMomentAverage X k ≤ A ∧
          ∃ a : α, T < X a) := by
  constructor
  · intro hrate X hX havg
    exact forall_le_of_averageMoment_card_mul_le_threshold hX hT hk havg hrate
  · intro S hS hTS hbudget
    exact averageMoment_budget_allows_single_spike_of_pow_le_card_mul
      (α := α) hk hS hTS hbudget

#print axioms powMomentSum_le_card_mul_of_average_le
#print axioms single_pow_le_powMomentSum
#print axioms forall_le_of_powMomentSum_le_threshold
#print axioms forall_le_of_averageMoment_card_mul_le_threshold
#print axioms forall_le_of_averageMoment_card_mul_lt_threshold
#print axioms powMomentSum_single_spike
#print axioms powMomentAverage_single_spike
#print axioms averageMoment_budget_allows_single_spike
#print axioms averageMoment_budget_allows_single_spike_of_pow_le_card_mul
#print axioms momentTailRateGate

end ArkLib.ProximityGap.Frontier.MomentTailRateGate
