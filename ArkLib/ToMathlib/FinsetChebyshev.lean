/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FinsetMarkov

/-!
# Chebyshev's inequality over a finite type (concentration count bound)

The discrete Chebyshev inequality, obtained by applying Markov (`FinsetMarkov`) to the squared
deviation `(X - μ)²`: over a `Fintype`, the deviation level set is small,

  `#{ i : a ≤ |X i - μ| } ≤ (∑ i, (X i - μ)²) / a²`.

In probabilistic terms (uniform law, `μ = E[X]`): `Pr[|X - E[X]| ≥ a] ≤ Var[X] / a²`. This is the
concentration tool complementing Markov (`FinsetMarkov`) and the second-moment method
(`SecondMomentProb`) for random-code / random-domain tail bounds.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `card_filter_abs_sub_ge_le_sum_sq_div`.
-/

namespace ArkLib

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Chebyshev (count form).** For any center `μ` and `a > 0`,
`#{i : a ≤ |X i - μ|} ≤ (∑ i, (X i - μ)²) / a²`. With `μ = E[X]` and the uniform law this is
`Pr[|X - E[X]| ≥ a] ≤ Var[X] / a²`. -/
theorem card_filter_abs_sub_ge_le_sum_sq_div (X : ι → ℝ) (μ a : ℝ) (ha : 0 < a) :
    ((Finset.univ.filter (fun i => a ≤ |X i - μ|)).card : ℝ)
      ≤ (∑ i, (X i - μ) ^ 2) / a ^ 2 := by
  classical
  have hsq : 0 < a ^ 2 := pow_pos ha 2
  have hsub :
      (Finset.univ.filter (fun i => a ≤ |X i - μ|))
        ⊆ (Finset.univ.filter (fun i => a ^ 2 ≤ (X i - μ) ^ 2)) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have h2 := pow_le_pow_left₀ ha.le hi.2 2
    rwa [sq_abs] at h2
  calc ((Finset.univ.filter (fun i => a ≤ |X i - μ|)).card : ℝ)
      ≤ ((Finset.univ.filter (fun i => a ^ 2 ≤ (X i - μ) ^ 2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (∑ i, (X i - μ) ^ 2) / a ^ 2 :=
        card_filter_ge_le_sum_div (fun i => (X i - μ) ^ 2) (a ^ 2) hsq (fun i => sq_nonneg _)

end ArkLib

-- Axiom audit.
#print axioms ArkLib.card_filter_abs_sub_ge_le_sum_sq_div
