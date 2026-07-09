/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R221 zero-threshold survival obstruction)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer

/-!
# R221 (#466): the zero-threshold obstruction for survival envelopes

The R216 finite-grid consumer is sound, but any exponential survival envelope
used as its `NonzeroNormalizedSqGridTail` input must treat the `θ = 0` grid
point honestly.  At `θ = 0`, every nonzero frequency survives because
`0 ≤ ‖η_G(b)‖² / σ²`.  Therefore a bulk envelope with coefficient `< 1`
cannot include `0` unless its spike reserve pays the missing carrier mass.

This records the obstruction as a Lean theorem, matching the R221 optimizer
probe.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R221ZeroThresholdSurvivalObstruction

open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- At threshold zero, the survival count is the full nonzero-frequency
carrier. -/
theorem full_carrier_le_tail_at_zero
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    (Θ : Finset ℝ) (B : ℝ → ℝ)
    (hzero : (0 : ℝ) ∈ Θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ B) :
    (((nonzeroFreqs (F := F)).card : ℝ)) ≤ B 0 := by
  have hsubset :
      nonzeroFreqs (F := F) ⊆
        (nonzeroFreqs (F := F)).filter
          (fun b => (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2) := by
    intro b hb
    simp [hb, div_nonneg (sq_nonneg ‖eta ψ G b‖) (sq_nonneg σ)]
  exact le_trans (by exact_mod_cast Finset.card_le_card hsubset) (hTail 0 hzero)

/-- The literal `(3/5, K)` half-rate envelope can contain `θ = 0` only if
the spike reserve covers the missing `2/5` of the carrier. -/
theorem threeFifths_zero_tail_forces_spike_budget
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    (Θ : Finset ℝ) (Kspike : ℝ)
    (hzero : (0 : ℝ) ∈ Θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + Kspike)) :
    (2 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) ≤ Kspike := by
  have hfull := full_carrier_le_tail_at_zero ψ G σ Θ
    (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
      Real.exp (-(θ / 2)) + Kspike) hzero hTail
  have hexp : Real.exp (-((0 : ℝ) / 2)) = 1 := by norm_num
  nlinarith

end ArkLib.ProximityGap.Frontier.R221ZeroThresholdSurvivalObstruction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R221ZeroThresholdSurvivalObstruction.full_carrier_le_tail_at_zero
#print axioms ArkLib.ProximityGap.Frontier.R221ZeroThresholdSurvivalObstruction.threeFifths_zero_tail_forces_spike_budget
