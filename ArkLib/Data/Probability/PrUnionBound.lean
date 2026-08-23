/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Instances

/-!
# Union bounds for the `Pr_{...}[...]` notation

This file proves finset union bounds for ArkLib's PMF-bind-based, `ENNReal`-valued
probability notation `Pr_{ let x ← D }[ P x ]`:

* `PrUnion.Pr_false`: the probability of the `False` event is `0`;
* `PrUnion.Pr_mono`: monotonicity of `Pr_` in the event;
* `PrUnion.Pr_or_le`: the binary union bound `Pr[P ∨ Q] ≤ Pr[P] + Pr[Q]`;
* `PrUnion.Pr_finset_exists_le_sum`: the finset union bound
  `Pr[∃ y ∈ s, Q y x] ≤ ∑ y ∈ s, Pr[Q y x]`;
* `PrUnion.Pr_finset_exists_le_card_mul`: the cardinality-times-uniform-bound corollary.

All proofs go through the tsum unrolling `prob_tsum_form_singleton` from
`ArkLib.Data.Probability.Instances`.
-/

open ProbabilityTheory

namespace PrUnion

variable {α β : Type}

/-- The probability of the `False` event is `0`. -/
lemma Pr_false (D : PMF α) : Pr_{ let _x ← D }[ False ] = 0 := by
  classical
  rw [prob_tsum_form_singleton D (fun _ => False)]
  simp

/-- Monotonicity of `Pr_` in the event: if `P x → Q x` pointwise, then
`Pr[P] ≤ Pr[Q]`. -/
lemma Pr_mono (D : PMF α) (P Q : α → Prop) (h : ∀ x, P x → Q x) :
    Pr_{ let x ← D }[ P x ] ≤ Pr_{ let x ← D }[ Q x ] := by
  classical
  simp_rw [prob_tsum_form_singleton]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul_right ?_ _
  by_cases hp : P x
  · simp [hp, h x hp]
  · simp [hp]

/-- Binary union bound: `Pr[P ∨ Q] ≤ Pr[P] + Pr[Q]`. -/
lemma Pr_or_le (D : PMF α) (P Q : α → Prop) :
    Pr_{ let x ← D }[ P x ∨ Q x ] ≤
      Pr_{ let x ← D }[ P x ] + Pr_{ let x ← D }[ Q x ] := by
  classical
  simp_rw [prob_tsum_form_singleton]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  calc D x * (if P x ∨ Q x then 1 else 0)
      ≤ D x * ((if P x then 1 else 0) + (if Q x then 1 else 0)) := by
        refine mul_le_mul_right ?_ _
        by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
    _ = D x * (if P x then 1 else 0) + D x * (if Q x then 1 else 0) := mul_add _ _ _

/-- **Finset union bound.** The probability that some `y ∈ s` satisfies `Q y x`
is at most the sum over `y ∈ s` of the individual probabilities. -/
lemma Pr_finset_exists_le_sum (D : PMF α) (s : Finset β) (Q : β → α → Prop) :
    Pr_{ let x ← D }[ ∃ y ∈ s, Q y x ] ≤ ∑ y ∈ s, Pr_{ let x ← D }[ Q y x ] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hP : Pr_{ let x ← D }[ ∃ y ∈ (∅ : Finset β), Q y x ] =
          Pr_{ let x ← D }[ False ] :=
        Pr_congr fun x => by simp
      rw [hP, Pr_false D, Finset.sum_empty]
  | @insert a t ha ih =>
      have hP : Pr_{ let x ← D }[ ∃ y ∈ insert a t, Q y x ] =
          Pr_{ let x ← D }[ Q a x ∨ ∃ y ∈ t, Q y x ] :=
        Pr_congr fun x => by simp
      rw [hP, Finset.sum_insert ha]
      exact le_trans (Pr_or_le D (Q a) (fun x => ∃ y ∈ t, Q y x)) (add_le_add le_rfl ih)

/-- Convenience corollary: if every individual event has probability at most `c`,
the union over `s` has probability at most `s.card * c`. -/
lemma Pr_finset_exists_le_card_mul (D : PMF α) (s : Finset β) (Q : β → α → Prop)
    (c : ENNReal) (hc : ∀ y ∈ s, Pr_{ let x ← D }[ Q y x ] ≤ c) :
    Pr_{ let x ← D }[ ∃ y ∈ s, Q y x ] ≤ s.card * c := by
  refine le_trans (Pr_finset_exists_le_sum D s Q) (le_trans (Finset.sum_le_sum hc) ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

end PrUnion

#print axioms PrUnion.Pr_false
#print axioms PrUnion.Pr_mono
#print axioms PrUnion.Pr_or_le
#print axioms PrUnion.Pr_finset_exists_le_sum
#print axioms PrUnion.Pr_finset_exists_le_card_mul
