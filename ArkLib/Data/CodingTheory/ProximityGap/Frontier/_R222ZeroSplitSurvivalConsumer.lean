/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R222 zero-split survival consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer

/-!
# R222 (#466): zero-split survival consumer

R221 proved that a bulk coefficient below `1` cannot honestly cover the
`θ = 0` survival count.  This file packages the corrected R216 socket:

* at `θ = 0`, pay the full nonzero-frequency carrier;
* at `θ ≠ 0`, use the proposed exponential bulk-plus-spikes tail.

The analytic tail remains an explicit input.  The point is to prevent the
impossible unsplit `(3/5) exp(-θ/2) + 2` hypothesis from entering future MGF
closures.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R222ZeroSplitSurvivalConsumer

open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The corrected zero-split tail envelope: full carrier at `θ = 0`, and the
bulk-plus-spikes formula away from zero. -/
noncomputable def zeroSplitBulkSpikesBound (Cbulk Kspike : ℝ) (θ : ℝ) : ℝ :=
  if θ = 0 then
    ((nonzeroFreqs (F := F)).card : ℝ)
  else
    Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) * Real.exp (-(θ / 2)) + Kspike

/-- A positive-threshold tail automatically extends to the zero-split grid
tail, because the zero threshold is paid by the full carrier. -/
theorem zeroSplitGridTail_of_positive_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (Cbulk Kspike : ℝ)
    (hPosTail : ∀ θ ∈ Θ, θ ≠ 0 →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + Kspike) :
    NonzeroNormalizedSqGridTail ψ G σ Θ
      (zeroSplitBulkSpikesBound (F := F) Cbulk Kspike) := by
  intro θ hθ
  by_cases hzero : θ = 0
  · subst θ
    simp only [zeroSplitBulkSpikesBound, ↓reduceIte]
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset
        (fun b => (0 : ℝ) ≤ ‖eta ψ G b‖ ^ (2 : ℕ) / σ ^ (2 : ℕ))
        (nonzeroFreqs (F := F)))
  · simpa [zeroSplitBulkSpikesBound, hzero] using hPosTail θ hθ hzero

/-- The corrected zero-split bulk-plus-spikes survival envelope implies the
R213 normalized-square quarter-MGF residual once its weighted staircase budget
fits under `2 * carrier`. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_bulkPlusSpikes_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hPosTail : ∀ θ ∈ Θ, θ ≠ 0 →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + Kspike)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * zeroSplitBulkSpikesBound (F := F) Cbulk Kspike θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
    ψ G Θ δ (zeroSplitBulkSpikesBound (F := F) Cbulk Kspike)
    hδ hstair
    (zeroSplitGridTail_of_positive_tail ψ G Θ Cbulk Kspike hPosTail)
    hweighted

/-- Literal `(3/5, 2)` zero-split specialization.  The zero bin is no longer
covered by `3/5`; it is paid exactly by the carrier term. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_threeFifths_plus_two_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hPosTail : ∀ θ ∈ Θ, θ ≠ 0 →
      (((nonzeroFreqs (F := F)).filter
        (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤
          (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
            Real.exp (-(θ / 2)) + 2)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * zeroSplitBulkSpikesBound (F := F) (3 / 5) 2 θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_bulkPlusSpikes_tail
    ψ G Θ δ (3 / 5) 2 hδ hstair hPosTail hweighted

end ArkLib.ProximityGap.Frontier.R222ZeroSplitSurvivalConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R222ZeroSplitSurvivalConsumer.zeroSplitGridTail_of_positive_tail
#print axioms ArkLib.ProximityGap.Frontier.R222ZeroSplitSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_bulkPlusSpikes_tail
#print axioms ArkLib.ProximityGap.Frontier.R222ZeroSplitSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_zeroSplit_threeFifths_plus_two_tail
