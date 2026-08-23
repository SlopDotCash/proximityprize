/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev

/-!
# Cauchy-Schwarz support bound (Paley-Zygmund numerator)

`(∑ a, f a)² ≤ |support f| · (∑ a, f a²)` for `f : α → ℕ` over a finite type.  Equivalently the
support of `f` has size at least `(∑ f)² / (∑ f²)` — the Paley-Zygmund first and second moment lower
bound on the number of nonzero coordinates.

This is the generic engine behind the CS25 issue-82 covering count: with
`f w = #{c ∈ C : Δ(w,c) ≤ δn}`, the first moment `∑ f = |C|·V` and a second-moment bound `∑ f²`
together lower-bound the *covered* set `support f = {w : Δᵣ(w,C) ≤ δ}`.
-/

open scoped BigOperators

namespace ArkLib

/-- **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ |support f| · (∑ f²)`. -/
theorem sq_sum_le_card_support_mul_sum_sq {α : Type*} [Fintype α] (f : α → ℕ) :
    (∑ a, f a) ^ 2
      ≤ (Finset.univ.filter (fun a => f a ≠ 0)).card * (∑ a, f a ^ 2) := by
  classical
  have hsum : (∑ a, f a)
      = ∑ a ∈ Finset.univ.filter (fun a => f a ≠ 0), f a := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro a _ ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
    exact ha
  rw [hsum]
  have hsub : Finset.univ.filter (fun a => f a ≠ 0) ⊆ (Finset.univ : Finset α) :=
    Finset.filter_subset _ _
  refine le_trans sq_sum_le_card_mul_sum_sq (mul_le_mul' le_rfl ?_)
  exact Finset.sum_le_sum_of_subset hsub

end ArkLib
