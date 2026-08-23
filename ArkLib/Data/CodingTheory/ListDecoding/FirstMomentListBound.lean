/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# The first-moment list-size bound (union-bound shell of the FPRUNE argument)

The list-decoding bound for subspace-design codes (Chen–Zhang 2025 Thm B.5 / arXiv 2512.08017
Thm 3.6, the gating input for ABF26 §4 T4.13 and CZ25 C3.5) is proven by a first-moment /
union-bound argument over a distribution of coordinate sets produced by the `FPRUNE` algorithm:

* (Lemma 3.5) each candidate codeword `c` has expected weighted agreement `≥ β`;
* (the subspace-design budget) the *total* weighted agreement over the candidate list is `≤ M`
  pointwise in the sample;

so by linearity of expectation `|L| · β ≤ E[total] ≤ M`, hence `|L| ≤ M / β`.

This file proves that union-bound shell **abstractly and elementarily**, with the "expectation"
modelled as a finite weighted average (a probability mass `p` on a finite sample space `Ω` with
`∑ p = 1`, `p ≥ 0`). This isolates the genuine remaining cores of the list bound — the per-codeword
lower bound (Lemma 3.5) and the design-budget pointwise bound — as the two clean hypotheses
`hLower` / `hSimul`, exactly the reduction the in-tree `sum_card_vanishing_le_design` (the
subspace-design inequality, Def 6) is meant to feed.

No coding-theory or measure-theoretic dependencies: pure `Finset` arithmetic, reusable for any
first-moment list bound.
-/

namespace CodingTheory.ListDecoding

open Finset

variable {α Ω : Type*}

/-- **First-moment list-size bound (union-bound shell).** Let `p` be a probability mass on a
finite sample space `Ω` (`∑ p = 1`, `p ≥ 0`), and `g c T` a nonnegative weighted-agreement score
for candidate `c` on sample `T`. If every candidate in the list `L` has expected score at least
`β > 0` (Lemma 3.5), and the *total* score over `L` is at most `M` pointwise (the design budget),
then `|L| · β ≤ M`.

Proof: linearity of expectation, `|L|·β ≤ ∑_c E[g c] = E[∑_c g c] ≤ E[M] = M`. -/
theorem card_mul_le_of_expectation_bounds
    [Fintype Ω] (p : Ω → ℝ) (hp_nonneg : ∀ T, 0 ≤ p T) (hp_sum : ∑ T, p T = 1)
    (L : Finset α) (g : α → Ω → ℝ) (β M : ℝ)
    (hLower : ∀ c ∈ L, β ≤ ∑ T, p T * g c T)
    (hSimul : ∀ T, (∑ c ∈ L, g c T) ≤ M) :
    (L.card : ℝ) * β ≤ M := by
  calc (L.card : ℝ) * β
      = ∑ _c ∈ L, β := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ L, ∑ T, p T * g c T := Finset.sum_le_sum hLower
    _ = ∑ T, p T * (∑ c ∈ L, g c T) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ T, p T * M := by
        refine Finset.sum_le_sum (fun T _ => ?_)
        exact mul_le_mul_of_nonneg_left (hSimul T) (hp_nonneg T)
    _ = M := by rw [← Finset.sum_mul, hp_sum, one_mul]

/-- **List-size bound from the first moment.** With `β > 0`, the shell yields `|L| ≤ M / β`. -/
theorem card_le_of_expectation_bounds
    [Fintype Ω] (p : Ω → ℝ) (hp_nonneg : ∀ T, 0 ≤ p T) (hp_sum : ∑ T, p T = 1)
    (L : Finset α) (g : α → Ω → ℝ) (β M : ℝ) (hβ : 0 < β)
    (hLower : ∀ c ∈ L, β ≤ ∑ T, p T * g c T)
    (hSimul : ∀ T, (∑ c ∈ L, g c T) ≤ M) :
    (L.card : ℝ) ≤ M / β := by
  rw [le_div_iff₀ hβ]
  exact card_mul_le_of_expectation_bounds p hp_nonneg hp_sum L g β M hLower hSimul

/-- **List-size bound from un-normalized weights.** If `w` is a nonnegative finite weight
function with total mass `W > 0`, the first-moment shell can be applied after normalizing
`p T = w T / W`. This is the feeder form used by FPRUNE-style arguments that naturally produce
unnormalized coordinate-set weights. -/
theorem card_le_of_weight_bounds
    [Fintype Ω] (w : Ω → ℝ) (hw_nonneg : ∀ T, 0 ≤ w T)
    (W : ℝ) (hW : 0 < W) (hWsum : W = ∑ T, w T)
    (L : Finset α) (g : α → Ω → ℝ) (β M : ℝ) (hβ : 0 < β)
    (hLower : ∀ c ∈ L, β * W ≤ ∑ T, w T * g c T)
    (hSimul : ∀ T, (∑ c ∈ L, g c T) ≤ M) :
    (L.card : ℝ) ≤ M / β := by
  let p : Ω → ℝ := fun T => w T / W
  have hp_nonneg : ∀ T, 0 ≤ p T := fun T => div_nonneg (hw_nonneg T) (le_of_lt hW)
  have hp_sum : ∑ T, p T = 1 := by
    simp only [p]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← hWsum]
    exact mul_inv_cancel₀ (ne_of_gt hW)
  have hLower' : ∀ c ∈ L, β ≤ ∑ T, p T * g c T := by
    intro c hc
    have hsum : ∑ T, p T * g c T = (∑ T, w T * g c T) / W := by
      simp only [p]
      simp only [div_eq_mul_inv]
      calc
        ∑ T, (w T * W⁻¹) * g c T = ∑ T, (w T * g c T) * W⁻¹ := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [mul_assoc, mul_comm W⁻¹ (g c T), ← mul_assoc]
        _ = (∑ T, w T * g c T) * W⁻¹ := by rw [← Finset.sum_mul]
        _ = (∑ T, w T * g c T) / W := by rw [div_eq_mul_inv]
    rw [hsum, le_div_iff₀ hW]
    exact hLower c hc
  exact card_le_of_expectation_bounds p hp_nonneg hp_sum L g β M hβ hLower' hSimul

#print axioms CodingTheory.ListDecoding.card_le_of_weight_bounds

end CodingTheory.ListDecoding
