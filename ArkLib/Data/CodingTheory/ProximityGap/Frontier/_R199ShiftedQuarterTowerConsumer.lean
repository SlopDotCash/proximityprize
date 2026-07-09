/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R199 shifted-quarter tower consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R168DyadicTailEnvelopeConsumer

/-!
# R199 (#466): shifted-quarter tower consumer

R198 observed that the dyadic product-MGF budget can be bounded by a single
child quarter-MGF bound when the two child lists are shifts of the same
spectrum.  This file wires that observation directly to R168:

```text
parent_i <= left_i + right_i
sum exp(right_i/4) <= sum exp(left_i/4)
sum exp(left_i/4) <= 2 |s|
------------------------------------------------
DyadicTailMGFBound parent
```

The remaining analytic task is now sharply stated:

* prove the one-level quarter-MGF bound for the child spectrum, using the
  small-direct / large-tail split;
* prove the right-child quarter sum is the same as the left one (a quotient
  shift/permutation fact for the actual dyadic tower).
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R199ShiftedQuarterTowerConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

/-- AM-GM/Cauchy shortcut: the paired rate-`1/8` product budget is bounded by
the left rate-`1/4` budget if the right rate-`1/4` budget is no larger. -/
theorem productBudget_le_leftQuarter_of_rightQuarter_le {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ)
    (hRightLeLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤
        ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) :
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i))
      ≤ ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i) := by
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

/-- **Shifted-quarter tower consumer.**  A single child quarter-MGF bound is
enough for the R168 parent tail residual if the other child has no larger
quarter sum. -/
theorem dyadicTailMGF_of_shifted_child_quarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hRightLeLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤
        ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  refine dyadicTailMGF_of_tower_product_budget s parent left right hparent ?_
  exact (productBudget_le_leftQuarter_of_rightQuarter_le s left right hRightLeLeft).trans hLeft

end ArkLib.ProximityGap.Frontier.R199ShiftedQuarterTowerConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R199ShiftedQuarterTowerConsumer.productBudget_le_leftQuarter_of_rightQuarter_le
#print axioms ArkLib.ProximityGap.Frontier.R199ShiftedQuarterTowerConsumer.dyadicTailMGF_of_shifted_child_quarter
