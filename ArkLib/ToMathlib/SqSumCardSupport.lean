/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Chebyshev

/-! # Support version of the Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`

`(∑ f)² ≤ |{a : f a ≠ 0}| · ∑ f²` — the square of the sum is bounded by the number of *nonzero*
terms times the sum of squares.  This is the second-moment / Paley–Zygmund core
(`|support f| ≥ (∑ f)² / (∑ f²)`), used for δ-neighbourhood covering (ABF26 #82) and random-RS
variance bounds (#99). -/

open Finset

namespace Finset

variable {α R : Type*} [Fintype α] [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

theorem sq_sum_le_card_support_mul_sum_sq (f : α → R) :
    (∑ a, f a) ^ 2 ≤ (univ.filter (fun a => f a ≠ 0)).card * (∑ a, f a ^ 2) := by
  classical
  have hsub : (univ.filter (fun a => f a ≠ 0)) ⊆ (univ : Finset α) := filter_subset _ _
  have e1 : (∑ a, f a) = ∑ a ∈ univ.filter (fun a => f a ≠ 0), f a := by
    refine (Finset.sum_subset hsub ?_).symm
    intro a _ ha
    simp only [mem_filter, mem_univ, true_and, not_not] at ha
    exact ha
  have e2 : (∑ a, f a ^ 2) = ∑ a ∈ univ.filter (fun a => f a ≠ 0), f a ^ 2 := by
    refine (Finset.sum_subset hsub ?_).symm
    intro a _ ha
    simp only [mem_filter, mem_univ, true_and, not_not] at ha
    simp [ha]
  rw [e1, e2]
  exact sq_sum_le_card_mul_sum_sq

end Finset
