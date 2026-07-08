/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R198 shift-Cauchy product consumer)
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer

/-!
# R198 (#466): shifted-Cauchy shortcut for the dyadic product budget

R192/R193 reduced the dyadic product-MGF route to a covariance bound.  There
is an even more elementary sufficient condition in the actual dyadic tower:
the two child lists are the same spectrum with a quotient shift.  Hence their
square sums agree.  Pointwise `uv <= (u^2 + v^2)/2`, so

```text
avg_i u_i v_i <= avg_i u_i^2
```

whenever `sum v_i^2 <= sum u_i^2`.  With
`u_i = exp(left_i/8)` and `v_i = exp(right_i/8)`, this says the paired product
budget is bounded by the one-level quarter-MGF budget.

This is not a closure of the prize: it moves the analytic target to the
one-level quarter-MGF bound, plus the finite small-index / large-index split.
It does remove the need for a separate half-turn covariance theorem.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer

/-- Product sum is bounded by the left square sum when the right square sum is
no larger.  This is just `2uv <= u^2+v^2`, summed. -/
theorem sum_mul_le_sum_sq_of_sum_sq_le {ι : Type*}
    (s : Finset ι) (u v : ι → ℝ)
    (hsq : (∑ i ∈ s, (v i) ^ 2) ≤ ∑ i ∈ s, (u i) ^ 2) :
    (∑ i ∈ s, u i * v i) ≤ ∑ i ∈ s, (u i) ^ 2 := by
  have hpoint : ∀ i ∈ s, u i * v i ≤ ((u i) ^ 2 + (v i) ^ 2) / 2 := by
    intro i _
    have hnonneg : 0 ≤ (u i - v i) ^ 2 := sq_nonneg (u i - v i)
    nlinarith
  calc
    (∑ i ∈ s, u i * v i)
        ≤ ∑ i ∈ s, (((u i) ^ 2 + (v i) ^ 2) / 2) := Finset.sum_le_sum hpoint
    _ = ((∑ i ∈ s, (u i) ^ 2) + (∑ i ∈ s, (v i) ^ 2)) / 2 := by
      simp [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
    _ ≤ ((∑ i ∈ s, (u i) ^ 2) + (∑ i ∈ s, (u i) ^ 2)) / 2 := by
      have hsum := add_le_add_right hsq (∑ i ∈ s, (u i) ^ 2)
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    _ = ∑ i ∈ s, (u i) ^ 2 := by ring

/-- Exponential form: the paired rate-`1/8` product budget is bounded by the
left rate-`1/4` MGF budget if the right square budget is no larger. -/
theorem exp_productBudget_le_left_quarterBudget {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2) :
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i))
      ≤ ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i) := by
  have h := sum_mul_le_sum_sq_of_sum_sq_le s
    (fun i => Real.exp ((1 / 8 : ℝ) * left i))
    (fun i => Real.exp ((1 / 8 : ℝ) * right i)) hsq
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- If the right child is a square-budget shift of the left child and the left
quarter-MGF budget is at most `A |s|`, then the paired product budget is also
at most `A |s|`. -/
theorem productBudget_le_of_shifted_quarterMGF {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ) {A : ℝ}
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hLeftQuarter :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ A * (s.card : ℝ)) :
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i)) ≤ A * (s.card : ℝ) :=
  (exp_productBudget_le_left_quarterBudget s left right hsq).trans hLeftQuarter

/-- Named dyadic-quarter form: if the right child is square-sum dominated by
the left child and the left child satisfies the R188 quarter-MGF residual, then
the paired product budget is at most `2 |s|`. -/
theorem productBudget_le_two_of_shifted_dyadicQuarter {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hLeft : DyadicQuarterMGFBound s left) :
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i)) ≤ 2 * (s.card : ℝ) :=
  productBudget_le_of_shifted_quarterMGF s left right hsq
    (quarterMGF_sum_budget s left hLeft)

end ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.sum_mul_le_sum_sq_of_sum_sq_le
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.exp_productBudget_le_left_quarterBudget
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.productBudget_le_of_shifted_quarterMGF
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.productBudget_le_two_of_shifted_dyadicQuarter
