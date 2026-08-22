/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R216 nonzero normalized-square survival consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R213NonzeroNormalizedSqQuarterMGFResidualConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf

/-!
# R216 (#466): survival-grid consumer for the normalized-square residual

R213 named the remaining one-child analytic target as

```text
MGFBound (b ≠ 0) (fun b => ‖η_G(b)‖² / σ²) 2 (1/4).
```

This file specializes the existing S11 finite layer-cake/count-ceiling theorem
directly to that target.  The residual is now a concrete finite-grid survival
certificate for the normalized-square nonprincipal spectrum, matching the
R206/R213 probes:

```text
#{b ≠ 0 : θ ≤ ‖η_G(b)‖² / σ²} ≤ B(θ)
Σ_θ δ(θ) B(θ) ≤ 2 · #{b : b ≠ 0}.
```

No analytic tail estimate is proved here; this is the exact Lean-facing socket
for a proof of the observed half-rate survival law.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Survival-count ceiling on the nonzero normalized-square Gauss-period
spectrum. -/
def NonzeroNormalizedSqGridTail
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    (Θ : Finset ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Θ,
    (((nonzeroFreqs (F := F)).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤ B θ

/-- A finite survival-grid certificate implies the R213 normalized-square
quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ B : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ B)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * B θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact mgfBound_of_survival_count_ceiling
    (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2) Θ δ B
    hδ hstair hTail hweighted

/-- A half-rate bulk-plus-spikes survival envelope, packaged as a direct
residual for the normalized-square spectrum.  When the carrier is raw nonzero
frequencies, a two-coset spike reserve should be inserted here as a frequency
mass such as `Kspike = 2 * |G|`, not literal `2`. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_halfRate_bulkPlusSpikes_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Cbulk Kspike : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + Kspike))
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        (Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + Kspike))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
    ψ G Θ δ
    (fun θ => Cbulk * ((nonzeroFreqs (F := F)).card : ℝ) *
      Real.exp (-(θ / 2)) + Kspike)
    hδ hstair hTail hweighted

/-- Literal `(3/5, 2)` specialization.  This is appropriate for a carrier whose
spikes are counted as individual elements of `s`; for quotient-coset evidence
on raw frequencies, use `nonzeroNormalizedSqQuarterMGFResidual_of_halfRate_bulkPlusSpikes_tail`
with the spike budget multiplied by the coset multiplicity. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_threeFifths_plus_two_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : NonzeroNormalizedSqGridTail ψ G σ Θ
      (fun θ => (3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
        Real.exp (-(θ / 2)) + 2))
    (hweighted :
      (∑ θ ∈ Θ, δ θ *
        ((3 / 5 : ℝ) * ((nonzeroFreqs (F := F)).card : ℝ) *
          Real.exp (-(θ / 2)) + 2))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_halfRate_bulkPlusSpikes_tail
    ψ G Θ δ (3 / 5) 2 hδ hstair hTail hweighted

end ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
#print axioms ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_halfRate_bulkPlusSpikes_tail
#print axioms ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_threeFifths_plus_two_tail
