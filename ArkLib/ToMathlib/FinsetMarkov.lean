/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# Markov's inequality over a finite type (level-set count bound)

The discrete Markov inequality for a nonnegative function `f : ι → ℝ` over a `Fintype`: the level
set `{ f ≥ a }` is small,

  `#{ i : a ≤ f i } · a ≤ ∑ i, f i`,   equivalently  `#{ i : a ≤ f i } ≤ (∑ i, f i) / a`.

In probabilistic terms (uniform law): `Pr[f ≥ a] ≤ E[f] / a`. This is the upper-bound complement
to the second-moment method (`SecondMomentProb`); together they bound failure/soundness
probabilities and list-size tails for random-code / random-domain arguments.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `card_filter_ge_mul_le_sum` — `#{f ≥ a} · a ≤ ∑ f`.
* `card_filter_ge_le_sum_div` — `#{f ≥ a} ≤ (∑ f) / a`.
-/

namespace ArkLib

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Markov (core).** For nonnegative `f`, `#{i : a ≤ f i} · a ≤ ∑ i, f i`. -/
theorem card_filter_ge_mul_le_sum (f : ι → ℝ) (a : ℝ) (hf : ∀ i, 0 ≤ f i) :
    ((Finset.univ.filter (fun i => a ≤ f i)).card : ℝ) * a ≤ ∑ i, f i := by
  classical
  calc ((Finset.univ.filter (fun i => a ≤ f i)).card : ℝ) * a
      = ∑ _i ∈ Finset.univ.filter (fun i => a ≤ f i), a := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => a ≤ f i), f i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hf i)

/-- **Markov (count form).** For nonnegative `f` and `a > 0`, `#{i : a ≤ f i} ≤ (∑ i, f i) / a`. -/
theorem card_filter_ge_le_sum_div (f : ι → ℝ) (a : ℝ) (ha : 0 < a) (hf : ∀ i, 0 ≤ f i) :
    ((Finset.univ.filter (fun i => a ≤ f i)).card : ℝ) ≤ (∑ i, f i) / a := by
  rw [le_div_iff₀ ha]
  exact card_filter_ge_mul_le_sum f a hf

end ArkLib

-- Axiom audit.
#print axioms ArkLib.card_filter_ge_mul_le_sum
#print axioms ArkLib.card_filter_ge_le_sum_div
