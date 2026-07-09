/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R206 Gauss-period dilation prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R205GaussPeriodShiftPrizeConsumer

/-!
# R206 (#466): concrete dilation-recursion prize consumer

R205 consumed an abstract parent inequality

```text
parent b ≤ ‖η_G(b)‖ + ‖η_G(ζ*b)‖.
```

For the actual dyadic dilation parent
`parent b = ‖η_{G ∪ ζG}(b)‖`, this is exactly the already-proven
triangle-bound side of the dilation recursion, `eta_union_dilate_norm_le`.

This file removes that remaining bookkeeping hypothesis from the concrete
full-frequency shifted-quarter chain.  The only analytic input left at this
interface is the one-child quarter-MGF bound for `‖η_G(b)‖`.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Concrete dyadic-tail MGF residual for the actual dilation-recursion parent. -/
theorem dyadicTailMGF_of_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ)) :
    DyadicTailMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  refine dyadicTailMGF_of_gaussPeriod_shift_quarter ψ G hζ
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) ?_ hLeft
  intro b
  exact eta_union_dilate_norm_le ψ G hζ hdisj b

/-- Reindexed R198-route version of the concrete dyadic-tail residual for the
actual dilation-recursion parent. -/
theorem dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖)) :
    DyadicTailMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  refine dyadicTailMGF_of_gaussPeriod_reindexed_quarter ψ G hζ
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) ?_ hLeft
  intro b
  exact eta_union_dilate_norm_le ψ G hζ hdisj b

/-- Sum-bound version of the reindexed R198-route concrete dyadic-tail residual. -/
theorem dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ)) :
    DyadicTailMGFBound (Finset.univ : Finset F)
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  exact dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter ψ G hζ hdisj
    (by simpa [DyadicQuarterMGFBound] using hLeft)

/-- Prize-square endpoint for the actual dilation-recursion parent. -/
theorem prize_sq_of_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_gaussPeriod_shift_quarter ψ G hζ
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) ?_ hLeft
    hMmax hn hQ ?_ hP hr hrQ ?_
  · intro b
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · intro b
    exact norm_nonneg _
  · simpa using hmoment

/-- Reindexed R198-route prize-square endpoint for the actual
dilation-recursion parent. -/
theorem prize_sq_of_gaussPeriod_dilation_reindexed_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_gaussPeriod_reindexed_quarter ψ G hζ
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) ?_ hLeft
    hMmax hn hQ ?_ hP hr hrQ ?_
  · intro b
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · intro b
    exact norm_nonneg _
  · simpa using hmoment

/-- Sum-bound version of the reindexed R198-route prize-square endpoint for
the actual dilation-recursion parent. -/
theorem prize_sq_of_gaussPeriod_dilation_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_gaussPeriod_dilation_reindexed_quarter ψ G hζ hdisj
    (by simpa [DyadicQuarterMGFBound] using hLeft)
    hMmax hn hQ hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.dyadicTailMGF_of_gaussPeriod_dilation_quarter
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.dyadicTailMGF_of_gaussPeriod_dilation_reindexed_quarter_sum
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.prize_sq_of_gaussPeriod_dilation_quarter
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.prize_sq_of_gaussPeriod_dilation_reindexed_quarter
#print axioms ArkLib.ProximityGap.Frontier.R206GaussPeriodDilationPrizeConsumer.prize_sq_of_gaussPeriod_dilation_reindexed_quarter_sum
