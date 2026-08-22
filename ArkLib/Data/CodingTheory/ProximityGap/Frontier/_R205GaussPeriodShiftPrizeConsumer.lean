/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R205 Gauss-period shift prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R200ShiftedQuarterPrizeConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R198ShiftCauchyProductConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R204GaussPeriodShiftQuarterSum

/-!
# R205 (#466): concrete full-frequency Gauss-period shift consumer

R204 proves that the two children in the dilation recursion have the same
quarter-MGF sum over the full frequency set:

```text
left  b = ‖η_G(b)‖
right b = ‖η_G(ζ b)‖
```

This file wires that concrete equality into the R200 shifted-quarter consumer.
The only remaining analytic input at this interface is the one-child quarter-MGF
bound for the Gauss-period spectrum.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer

open ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer
open ArkLib.ProximityGap.Frontier.R198ShiftCauchyProductConsumer
open ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F]

/-- Concrete full-frequency dyadic-tail consumer for the Gauss-period dilation
children. -/
theorem dyadicTailMGF_of_gaussPeriod_shift_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ)
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ)) :
    DyadicTailMGFBound (Finset.univ : Finset F) parent := by
  refine dyadicTailMGF_of_shifted_quarter (Finset.univ : Finset F) parent
    (fun b => ‖eta ψ G b‖) (fun b => ‖eta ψ G (ζ * b)‖) ?_ ?_ ?_
  · intro b _
    exact hparent b
  · simpa using quarter_sum_eta_shift_le ψ G hζ
  · simpa using hLeft

/-- Concrete full-frequency dyadic-tail consumer for the Gauss-period dilation
children, routed through the R198 finite-reindexing square-budget bridge. -/
theorem dyadicTailMGF_of_gaussPeriod_reindexed_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ)
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖)) :
    DyadicTailMGFBound (Finset.univ : Finset F) parent := by
  refine dyadicTailMGF_of_reindexed_dyadicQuarter
    (Finset.univ : Finset F) parent
    (fun b => ‖eta ψ G b‖) (fun b => ‖eta ψ G (ζ * b)‖)
    (fun b => ζ * b) (fun c => ζ⁻¹ * c) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b _
    exact hparent b
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _
    exact Finset.mem_univ _
  · intro b _
    simp [hζ]
  · intro c _
    field_simp [hζ]
  · intro _ _
    rfl
  · exact hLeft

/-- Sum-bound version of `dyadicTailMGF_of_gaussPeriod_reindexed_quarter`. -/
theorem dyadicTailMGF_of_gaussPeriod_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ)
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ)) :
    DyadicTailMGFBound (Finset.univ : Finset F) parent := by
  exact dyadicTailMGF_of_gaussPeriod_reindexed_quarter ψ G hζ parent hparent
    (by simpa [DyadicQuarterMGFBound] using hLeft)

/-- Prize-square endpoint for the concrete full-frequency Gauss-period shift
consumer. -/
theorem prize_sq_of_gaussPeriod_shift_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ) {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b : F, 0 ≤ parent b)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b : F, (parent b) ^ r) / (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_shifted_quarter (Finset.univ : Finset F) parent
    (fun b => ‖eta ψ G b‖) (fun b => ‖eta ψ G (ζ * b)‖) ?_ ?_ ?_
    hMmax hn hQ ?_ ?_ hr hrQ ?_
  · intro b _
    exact hparent b
  · simpa using quarter_sum_eta_shift_le ψ G hζ
  · simpa using hLeft
  · intro b _
    exact ht b
  · simpa using hP
  · simpa using hmoment

/-- Prize-square endpoint for the concrete full-frequency Gauss-period shift,
routed through the R198 finite-reindexing bridge. -/
theorem prize_sq_of_gaussPeriod_reindexed_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ) {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft : DyadicQuarterMGFBound (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b : F, 0 ≤ parent b)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b : F, (parent b) ^ r) / (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_reindexed_dyadicQuarter
    (Finset.univ : Finset F) parent
    (fun b => ‖eta ψ G b‖) (fun b => ‖eta ψ G (ζ * b)‖)
    (fun b => ζ * b) (fun c => ζ⁻¹ * c) ?_ ?_ ?_ ?_ ?_ ?_
    hLeft hMmax hn hQ ?_ ?_ hr hrQ ?_
  · intro b _
    exact hparent b
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _
    exact Finset.mem_univ _
  · intro b _
    simp [hζ]
  · intro c _
    field_simp [hζ]
  · intro _ _
    rfl
  · intro b _
    exact ht b
  · simpa using hP
  · simpa using hmoment

/-- Sum-bound version of `prize_sq_of_gaussPeriod_reindexed_quarter`. -/
theorem prize_sq_of_gaussPeriod_reindexed_quarter_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (parent : F → ℝ) {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ b : F, parent b ≤ ‖eta ψ G b‖ + ‖eta ψ G (ζ * b)‖)
    (hLeft :
      (∑ b : F, Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * (Fintype.card F : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b : F, 0 ≤ parent b)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b : F, (parent b) ^ r) / (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_gaussPeriod_reindexed_quarter ψ G hζ parent hparent
    (by simpa [DyadicQuarterMGFBound] using hLeft)
    hMmax hn hQ ht hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.dyadicTailMGF_of_gaussPeriod_shift_quarter
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.dyadicTailMGF_of_gaussPeriod_reindexed_quarter
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.dyadicTailMGF_of_gaussPeriod_reindexed_quarter_sum
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.prize_sq_of_gaussPeriod_shift_quarter
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.prize_sq_of_gaussPeriod_reindexed_quarter
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.prize_sq_of_gaussPeriod_reindexed_quarter_sum
