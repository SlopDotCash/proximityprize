/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R205 Gauss-period shift prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R200ShiftedQuarterPrizeConsumer
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

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer

open ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer
open ArkLib.ProximityGap.Frontier.R204GaussPeriodShiftQuarterSum
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
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

end ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.dyadicTailMGF_of_gaussPeriod_shift_quarter
#print axioms
  ArkLib.ProximityGap.Frontier.R205GaussPeriodShiftPrizeConsumer.prize_sq_of_gaussPeriod_shift_quarter
