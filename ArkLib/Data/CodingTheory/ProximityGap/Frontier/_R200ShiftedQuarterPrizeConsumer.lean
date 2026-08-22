/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R200 shifted-quarter prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R168DyadicTailEnvelopeConsumer

/-!
# R200 (#466): shifted-quarter assumptions feed the prize-square consumer

The dyadic/product-MGF route has been simplified to a one-level quarter-MGF
target.  This file records the full deterministic chain:

```text
parent_i <= left_i + right_i
sum exp(right_i/4) <= sum exp(left_i/4)
sum exp(left_i/4) <= 2 |s|
------------------------------------------------
R168 DyadicTailMGFBound parent
------------------------------------------------
S11/R168 prize-square bound
```

No finite-field analytic estimate is proved here.  The remaining inputs are
exactly the one-level quarter-MGF bound (small-direct / large-tail split) and
the quotient-shift equality of the two child quarter sums.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

/-- Paired product budget from one shifted quarter-MGF budget. -/
theorem productBudget_le_of_shifted_quarter {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ)
    (hRightLeLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤
        ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ)) :
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
      Real.exp ((1 / 8 : ℝ) * right i)) ≤ 2 * (s.card : ℝ) := by
  have hpoint : ∀ i ∈ s,
      Real.exp ((1 / 8 : ℝ) * left i) * Real.exp ((1 / 8 : ℝ) * right i)
        ≤ (Real.exp ((1 / 4 : ℝ) * left i) +
            Real.exp ((1 / 4 : ℝ) * right i)) / 2 := by
    intro i _
    set u := Real.exp ((1 / 8 : ℝ) * left i)
    set v := Real.exp ((1 / 8 : ℝ) * right i)
    have hamgm : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by
      have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
      nlinarith
    have hu : u ^ 2 = Real.exp ((1 / 4 : ℝ) * left i) := by
      subst u
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hv : v ^ 2 = Real.exp ((1 / 4 : ℝ) * right i) := by
      subst v
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa [hu, hv] using hamgm
  calc
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
      Real.exp ((1 / 8 : ℝ) * right i))
        ≤ ∑ i ∈ s, (Real.exp ((1 / 4 : ℝ) * left i) +
            Real.exp ((1 / 4 : ℝ) * right i)) / 2 := Finset.sum_le_sum hpoint
    _ = ((∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) +
          (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i))) / 2 := by
      simp [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
    _ ≤ ((∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) +
          (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))) / 2 := by
      have hsum := add_le_add_right hRightLeLeft
        (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    _ = ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i) := by ring
    _ ≤ 2 * (s.card : ℝ) := hLeft

/-- Shifted one-child quarter-MGF assumptions imply the R168 tail-MGF residual
for the parent spectrum. -/
theorem dyadicTailMGF_of_shifted_quarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hRightLeLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤
        ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_tower_product_budget s parent left right hparent
    (productBudget_le_of_shifted_quarter s left right hRightLeLeft hLeft)

/-- Full R168/S11 prize-square consumer with the shifted one-child quarter-MGF
assumptions exposed directly. -/
theorem prize_sq_of_shifted_quarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hRightLeLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤
        ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_shifted_quarter s parent left right hparent hRightLeLeft hLeft)
    hmoment

end ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer.productBudget_le_of_shifted_quarter
#print axioms ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer.dyadicTailMGF_of_shifted_quarter
#print axioms ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer.prize_sq_of_shifted_quarter
