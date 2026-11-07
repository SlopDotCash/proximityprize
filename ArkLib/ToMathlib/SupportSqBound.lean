/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SqSumCardSupport

/-!
# Cauchy-Schwarz support bound (Paley-Zygmund numerator)

`(∑ a, f a)² ≤ |support f| · (∑ a, f a²)` for `f : α → ℕ` over a finite type.  Equivalently the
support of `f` has size at least `(∑ f)² / (∑ f²)` — the Paley-Zygmund first and second moment lower
bound on the number of nonzero coordinates.

This is the generic engine behind the CS25 issue-82 covering count: with
`f w = #{c ∈ C : Δ(w,c) ≤ δn}`, the first moment `∑ f = |C|·V` and a second-moment bound `∑ f²`
together lower-bound the *covered* set `support f = {w : Δᵣ(w,C) ≤ δ}`.

The natural-number statement is the `R = ℕ` instance of the generic
`Finset.sq_sum_le_card_support_mul_sum_sq` (`ArkLib.ToMathlib.SqSumCardSupport`); it is kept
under its `ArkLib` name as a thin compatibility wrapper rather than a second Cauchy–Schwarz proof.
-/

open scoped BigOperators

namespace ArkLib

/-- **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ |support f| · (∑ f²)`.
The `ℕ`-valued instance of `Finset.sq_sum_le_card_support_mul_sum_sq`. -/
theorem sq_sum_le_card_support_mul_sum_sq {α : Type*} [Fintype α] (f : α → ℕ) :
    (∑ a, f a) ^ 2
      ≤ (Finset.univ.filter (fun a => f a ≠ 0)).card * (∑ a, f a ^ 2) :=
  Finset.sq_sum_le_card_support_mul_sum_sq f

end ArkLib
