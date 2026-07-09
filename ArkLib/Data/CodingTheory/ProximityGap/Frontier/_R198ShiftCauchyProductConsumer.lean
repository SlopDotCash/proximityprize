/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R198 shift-Cauchy product consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R197SmallDirectLargeTailSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R201SmallDirectLargeNormalizedBudgets
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R203LargeIndexNormalizedBudgets

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

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R190BulkPlusSpikesQuarterMGF
open ArkLib.ProximityGap.Frontier.R192BulkSpikeBudgetSplit
open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer
open ArkLib.ProximityGap.Frontier.R197SmallDirectLargeTailSplit
open ArkLib.ProximityGap.Frontier.R201SmallDirectLargeNormalizedBudgets
open ArkLib.ProximityGap.Frontier.R203LargeIndexNormalizedBudgets
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

/-- A literal reindexing of the right child by the left child proves the square-budget
shift certificate consumed below.  The hypotheses expose explicit forward and inverse maps on
the finite index set `s`, so group/coset lanes can instantiate them without a new abstraction. -/
theorem squareBudget_le_of_reindex {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ) (shift unshift : ι → ι)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i)) :
    (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
      ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2 := by
  have heq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) =
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2 := by
    calc
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2)
          = ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left (shift i))) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hright i hi]
      _ = ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2 := by
            refine Finset.sum_nbij' shift unshift ?_ ?_ ?_ ?_ ?_
            · exact hshift
            · exact hunshift
            · exact hleftInv
            · exact hrightInv
            · intro i _
              rfl
  exact le_of_eq heq

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

/-- **Shifted one-child tower consumer.**  If the parent is bounded by the
sum of two children, the right child is square-sum dominated by a shift of the
left child, and the left child satisfies the quarter-MGF residual, then the
parent satisfies the R168 dyadic-tail residual. -/
theorem dyadicTailMGF_of_shifted_dyadicQuarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hLeft : DyadicQuarterMGFBound s left) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_tower_product_budget s parent left right hparent
    (productBudget_le_two_of_shifted_dyadicQuarter s left right hsq hLeft)

/-- Shifted one-child tower consumer with the square-budget shift supplied as an
explicit reindexing of the finite set. -/
theorem dyadicTailMGF_of_reindexed_dyadicQuarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLeft : DyadicQuarterMGFBound s left) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_dyadicQuarter s parent left right hparent
    (squareBudget_le_of_reindex s left right shift unshift hshift hunshift
      hleftInv hrightInv hright)
    hLeft

/-- Shifted tower consumer with the one child quarter-MGF supplied by the
R197 small-direct / large-grid-tail split. -/
theorem dyadicTailMGF_of_shifted_smallDirect_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : N ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_dyadicQuarter s parent left right hparent hsq
    (quarterMGF_of_smallDirect_or_largeGridTail s left Θ δ N Cbulk Kspike
      hδ hstair hSmall hTailLarge hWeightedLarge)

/-- Live `N = 32` version of the shifted small-direct / large-grid-tail tower
consumer. -/
theorem dyadicTailMGF_of_shifted_small32Direct_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : 32 ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_smallDirect_or_largeGridTail s parent left right Θ δ 32
    Cbulk Kspike hparent hsq hδ hstair hSmall hTailLarge hWeightedLarge

/-- Reindexed version of the R197 small-direct / large-grid-tail tower
consumer.  This is the finite-bijection-facing form needed by tower lanes:
the square-budget hypothesis is discharged by `squareBudget_le_of_reindex`. -/
theorem dyadicTailMGF_of_reindexed_smallDirect_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ) (Cbulk Kspike : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : N ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_smallDirect_or_largeGridTail s parent left right Θ δ N
    Cbulk Kspike hparent
    (squareBudget_le_of_reindex s left right shift unshift hshift hunshift
      hleftInv hrightInv hright)
    hδ hstair hSmall hTailLarge hWeightedLarge

/-- Live `N = 32` reindexed version of the R197 split tower consumer. -/
theorem dyadicTailMGF_of_reindexed_small32Direct_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : 32 ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_reindexed_smallDirect_or_largeGridTail s parent left right
    shift unshift Θ δ 32 Cbulk Kspike hparent hshift hunshift hleftInv hrightInv
    hright hδ hstair hSmall hTailLarge hWeightedLarge

/-- Shifted tower consumer with the one child quarter-MGF supplied by the R201
small-direct / large normalized-budget split. -/
theorem dyadicTailMGF_of_shifted_smallDirect_or_largeNormalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hBulkLarge : N ≤ s.card → NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMassLarge : N ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_dyadicQuarter s parent left right hparent hsq
    (quarterMGF_of_smallDirect_or_largeNormalizedBudgets s left Θ δ N
      Cbulk Kspike Bbulk Bspike Mper hδ hstair hSmall hTailLarge hBulkLarge
      hK hMassLarge hFit hBudget)

/-- Reindexed version of the R201 normalized-budget tower consumer. -/
theorem dyadicTailMGF_of_reindexed_smallDirect_or_largeNormalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hBulkLarge : N ≤ s.card → NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMassLarge : N ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_shifted_smallDirect_or_largeNormalizedBudgets s parent left right
    Θ δ N Cbulk Kspike Bbulk Bspike Mper hparent
    (squareBudget_le_of_reindex s left right shift unshift hshift hunshift
      hleftInv hrightInv hright)
    hδ hstair hSmall hTailLarge hBulkLarge hK hMassLarge hFit hBudget

/-- Live `N = 32`, `Cbulk = 3/5`, `Kspike = 2` reindexed normalized-budget
tower consumer. -/
theorem dyadicTailMGF_of_reindexed_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Bbulk Bspike Mper : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ (3 / 5) 2)
    (hBulkLarge : 32 ≤ s.card → NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMassLarge : 32 ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_reindexed_dyadicQuarter s parent left right shift unshift
    hparent hshift hunshift hleftInv hrightInv hright
    (quarterMGF_of_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
      s left Θ δ Bbulk Bspike Mper hδ hstair hSmall hTailLarge hBulkLarge
      hMassLarge hFit hBudget)

/-- Reindexed tower consumer with the one child quarter-MGF supplied by the
R203 large-index-only normalized-budget route.  This is the prize-tower-facing
form once medium-index counterexamples are excluded by an index lower bound. -/
theorem dyadicTailMGF_of_reindexed_largeIndex_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLarge : N ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hTail : BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hBulk : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_reindexed_dyadicQuarter s parent left right shift unshift
    hparent hshift hunshift hleftInv hrightInv hright
    (quarterMGF_of_largeIndex_normalizedBudgets s left Θ δ N
      Cbulk Kspike Bbulk Bspike Mper hLarge hδ hstair hTail hBulk
      hK hMass hFit hBudget)

/-- Live `N = 1024`, `Cbulk = 3/5`, `Kspike = 2` reindexed large-index
tower consumer. -/
theorem dyadicTailMGF_of_reindexed_large1024_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Bbulk Bspike Mper : ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLarge : 1024 ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hTail : BulkPlusSpikesGridTail s left Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_reindexed_largeIndex_normalizedBudgets s parent left right
    shift unshift Θ δ 1024 (3 / 5) 2 Bbulk Bspike Mper
    hparent hshift hunshift hleftInv hrightInv hright hLarge hδ hstair
    hTail hBulk (by norm_num) hMass hFit hBudget

/-- Prize-square consumer for the shifted one-child route.  This exposes the
actual endpoint: a parent decomposition, a square-budget shift certificate, and
one quarter-MGF child residual are enough to feed the R168/S11 prize-square
bridge. -/
theorem prize_sq_of_shifted_dyadicQuarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hLeft : DyadicQuarterMGFBound s left)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_shifted_dyadicQuarter s parent left right hparent hsq hLeft)
    hmoment

/-- Prize-square endpoint with the square-budget shift supplied as an explicit
reindexing of the finite set. -/
theorem prize_sq_of_reindexed_dyadicQuarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLeft : DyadicQuarterMGFBound s left)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_reindexed_dyadicQuarter s parent left right shift unshift
      hparent hshift hunshift hleftInv hrightInv hright hLeft)
    hmoment

/-- Prize-square endpoint with the one child quarter-MGF supplied by the R197
small-direct / large-grid-tail split. -/
theorem prize_sq_of_shifted_smallDirect_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (N : ℕ) (Cbulk Kspike : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : N ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_shifted_smallDirect_or_largeGridTail s parent left right Θ δ N
      Cbulk Kspike hparent hsq hδ hstair hSmall hTailLarge hWeightedLarge)
    hmoment

/-- Live `N = 32` prize-square endpoint for the shifted small-direct /
large-grid-tail split. -/
theorem prize_sq_of_shifted_small32Direct_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (Cbulk Kspike : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hsq :
      (∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * right i)) ^ 2) ≤
        ∑ i ∈ s, (Real.exp ((1 / 8 : ℝ) * left i)) ^ 2)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : 32 ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_shifted_smallDirect_or_largeGridTail s parent left right Θ δ 32
    Cbulk Kspike hparent hsq hδ hstair hSmall hTailLarge hWeightedLarge
    hMmax hn hQ ht hP hr hrQ hmoment

/-- Prize-square endpoint for the R197 split with the square-budget shift
supplied as an explicit finite-set reindexing. -/
theorem prize_sq_of_reindexed_smallDirect_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ) (Cbulk Kspike : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : N ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_reindexed_smallDirect_or_largeGridTail s parent left right
      shift unshift Θ δ N Cbulk Kspike hparent hshift hunshift hleftInv hrightInv
      hright hδ hstair hSmall hTailLarge hWeightedLarge)
    hmoment

/-- Live `N = 32` prize-square endpoint for the reindexed R197 split. -/
theorem prize_sq_of_reindexed_small32Direct_or_largeGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hWeightedLarge : 32 ≤ s.card →
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * (s.card : ℝ) * Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_reindexed_smallDirect_or_largeGridTail s parent left right
    shift unshift Θ δ 32 Cbulk Kspike hparent hshift hunshift hleftInv hrightInv
    hright hδ hstair hSmall hTailLarge hWeightedLarge
    hMmax hn hQ ht hP hr hrQ hmoment

/-- Prize-square endpoint for the R201 normalized-budget split with the
square-budget shift supplied as an explicit finite-set reindexing. -/
theorem prize_sq_of_reindexed_smallDirect_or_largeNormalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < N → DyadicQuarterMGFBound s left)
    (hTailLarge : N ≤ s.card → BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hBulkLarge : N ≤ s.card → NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMassLarge : N ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_reindexed_smallDirect_or_largeNormalizedBudgets
      s parent left right shift unshift Θ δ N Cbulk Kspike Bbulk Bspike Mper
      hparent hshift hunshift hleftInv hrightInv hright hδ hstair hSmall hTailLarge
      hBulkLarge hK hMassLarge hFit hBudget)
    hmoment

/-- Live `N = 32`, `Cbulk = 3/5`, `Kspike = 2` prize-square endpoint for
the reindexed normalized-budget split. -/
theorem prize_sq_of_reindexed_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Bbulk Bspike Mper : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hSmall : s.card < 32 → DyadicQuarterMGFBound s left)
    (hTailLarge : 32 ≤ s.card → BulkPlusSpikesGridTail s left Θ (3 / 5) 2)
    (hBulkLarge : 32 ≤ s.card → NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMassLarge : 32 ≤ s.card → StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_reindexed_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
      s parent left right shift unshift Θ δ Bbulk Bspike Mper hparent hshift hunshift
      hleftInv hrightInv hright hδ hstair hSmall hTailLarge hBulkLarge hMassLarge
      hFit hBudget)
    hmoment

/-- Prize-square endpoint for the R203 large-index-only normalized-budget route
with the square-budget shift supplied as an explicit finite-set reindexing. -/
theorem prize_sq_of_reindexed_largeIndex_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (N : ℕ)
    (Cbulk Kspike Bbulk Bspike Mper : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLarge : N ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hTail : BulkPlusSpikesGridTail s left Θ Cbulk Kspike)
    (hBulk : NormalizedBulkWeightedBudget Θ δ Cbulk ≤ Bbulk)
    (hK : 0 ≤ Kspike)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : Kspike * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_reindexed_largeIndex_normalizedBudgets
      s parent left right shift unshift Θ δ N Cbulk Kspike Bbulk Bspike Mper
      hparent hshift hunshift hleftInv hrightInv hright hLarge hδ hstair hTail
      hBulk hK hMass hFit hBudget)
    hmoment

/-- Live `N = 1024`, `Cbulk = 3/5`, `Kspike = 2` prize-square endpoint for
the reindexed large-index normalized-budget route. -/
theorem prize_sq_of_reindexed_large1024_threeFifths_plus_two_normalizedBudgets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (parent left right : ι → ℝ) (shift unshift : ι → ι)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Bbulk Bspike Mper : ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hshift : ∀ i ∈ s, shift i ∈ s)
    (hunshift : ∀ j ∈ s, unshift j ∈ s)
    (hleftInv : ∀ i ∈ s, unshift (shift i) = i)
    (hrightInv : ∀ j ∈ s, shift (unshift j) = j)
    (hright : ∀ i ∈ s, right i = left (shift i))
    (hLarge : 1024 ≤ s.card)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 4 : ℝ) * left b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ left b), δ θ)
    (hTail : BulkPlusSpikesGridTail s left Θ (3 / 5) 2)
    (hBulk : NormalizedBulkWeightedBudget Θ δ (3 / 5) ≤ Bbulk)
    (hMass : StaircaseMass Θ δ ≤ Mper * (s.card : ℝ))
    (hFit : 2 * Mper ≤ Bspike)
    (hBudget : Bbulk + Bspike ≤ 2)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_reindexed_largeIndex_normalizedBudgets s parent left right
    shift unshift Θ δ 1024 (3 / 5) 2 Bbulk Bspike Mper
    hparent hshift hunshift hleftInv hrightInv hright hLarge hδ hstair
    hTail hBulk (by norm_num) hMass hFit hBudget
    hMmax hn hQ ht hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.sum_mul_le_sum_sq_of_sum_sq_le
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.exp_productBudget_le_left_quarterBudget
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.squareBudget_le_of_reindex
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.productBudget_le_of_shifted_quarterMGF
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.productBudget_le_two_of_shifted_dyadicQuarter
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_shifted_dyadicQuarter
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_dyadicQuarter
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_shifted_smallDirect_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_shifted_small32Direct_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_smallDirect_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_small32Direct_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_shifted_smallDirect_or_largeNormalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_smallDirect_or_largeNormalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_largeIndex_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.dyadicTailMGF_of_reindexed_large1024_threeFifths_plus_two_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_shifted_dyadicQuarter
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_dyadicQuarter
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_shifted_smallDirect_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_shifted_small32Direct_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_smallDirect_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_small32Direct_or_largeGridTail
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_smallDirect_or_largeNormalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_small32Direct_or_large_threeFifths_plus_two_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_largeIndex_normalizedBudgets
#print axioms ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer.prize_sq_of_reindexed_large1024_threeFifths_plus_two_normalizedBudgets
