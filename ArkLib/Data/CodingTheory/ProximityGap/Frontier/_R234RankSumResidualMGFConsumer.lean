/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R234 rank-sum residual MGF consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer

/-!
# R234 (#466): direct top-rank payment plus residual survival tail

R234's numerical lane found the first post-exception quotient-MGF closure
shape that survives stress:

* pay a small top-rank set by a direct MGF contribution cap;
* prove a survival tail only on the residual carrier;
* combine the direct top contribution with the residual layer-cake budget.

This file formalizes that finite mechanism on the raw nonzero-frequency
carrier.  It does not prove the top-rank cap or the residual tail; those are
the analytic inputs exposed by the R234 probes.
-/

set_option linter.style.longLine false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R234RankSumResidualMGFConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- The residual raw carrier after removing the marked top-rank set. -/
def residualNonzeroFreqs (T : Finset F) : Finset F :=
  (nonzeroFreqs (F := F)).filter (fun b => b ∉ T)

/-- The marked top-rank part, intersected with the raw nonzero carrier. -/
def topNonzeroFreqs (T : Finset F) : Finset F :=
  (nonzeroFreqs (F := F)).filter (fun b => b ∈ T)

/-- Residual survival-count ceiling after removing the marked top-rank set. -/
def ResidualNormalizedSqGridTail
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    (T : Finset F) (Θ : Finset ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((((residualNonzeroFreqs (F := F) T).filter
      (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) ≤ B θ)

/-- Direct top-rank payment plus a residual survival-count ceiling implies the
normalized-square quarter-MGF residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_topRank_residual_tail
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (T : Finset F) (Θ : Finset ℝ) (δ B : ℝ → ℝ) (Atop : ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hTop :
      (∑ b ∈ topNonzeroFreqs (F := F) T,
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2))) ≤ Atop)
    (hstairResidual : ∀ b ∈ residualNonzeroFreqs (F := F) T,
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hTail : ResidualNormalizedSqGridTail ψ G σ T Θ B)
    (hweighted :
      Atop + (∑ θ ∈ Θ, δ θ * B θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  unfold NonzeroNormalizedSqQuarterMGFResidual MGFBound
  let s : Finset F := nonzeroFreqs (F := F)
  let f : F → ℝ := fun b =>
    Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2))
  have hResidualWeighted :
      (∑ b ∈ residualNonzeroFreqs (F := F) T, f b)
        ≤ ∑ θ ∈ Θ, δ θ * B θ := by
    calc
      (∑ b ∈ residualNonzeroFreqs (F := F) T, f b)
          ≤ ∑ θ ∈ Θ, δ θ *
              (((residualNonzeroFreqs (F := F) T).filter
                (fun b => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2)).card : ℝ) :=
        mgf_le_survival_weighted
          (residualNonzeroFreqs (F := F) T)
          (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2) Θ δ hδ hstairResidual
      _ ≤ ∑ θ ∈ Θ, δ θ * B θ := by
        apply Finset.sum_le_sum
        intro θ hθ
        exact mul_le_mul_of_nonneg_left (hTail θ hθ) (hδ θ hθ)
  have hsplit :
      (∑ b ∈ s, f b)
        = (∑ b ∈ topNonzeroFreqs (F := F) T, f b) +
          (∑ b ∈ residualNonzeroFreqs (F := F) T, f b) := by
    dsimp [s, topNonzeroFreqs, residualNonzeroFreqs]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := nonzeroFreqs (F := F)) (p := fun b => b ∈ T) (f := f)]
  calc
    (∑ b ∈ s, f b)
        = (∑ b ∈ topNonzeroFreqs (F := F) T, f b) +
          (∑ b ∈ residualNonzeroFreqs (F := F) T, f b) := hsplit
    _ ≤ Atop + (∑ θ ∈ Θ, δ θ * B θ) :=
      add_le_add hTop hResidualWeighted
    _ ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ) := hweighted

end

end ArkLib.ProximityGap.Frontier.R234RankSumResidualMGFConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R234RankSumResidualMGFConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_topRank_residual_tail
