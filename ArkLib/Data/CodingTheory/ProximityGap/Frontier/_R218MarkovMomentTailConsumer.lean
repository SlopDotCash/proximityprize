/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R218 Markov moment tail consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R216NonzeroNormalizedSqSurvivalConsumer

/-!
# R218 (#466): Markov moment certificates for the normalized-square tail

R216 reduces the live normalized-square quarter-MGF residual to finite-grid
survival counts.  This file records the elementary but useful bridge from
moment estimates to those grid counts:

```text
θ^r · #{b ∈ s : θ ≤ t_b} ≤ Σ_{b∈s} t_b^r.
```

Thus a per-threshold choice of moment order `r(θ)` and moment ceiling gives
exactly the `NonzeroNormalizedSqGridTail` hypothesis consumed by R216.

No moment estimate is proved here.  The point is to make the proposed route
auditable: if a Wick/sub-exponential moment theorem is strong enough, it can
feed this file and then R216; if not, the obstruction is visible in the
threshold-wise budgets.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R218MarkovMomentTailConsumer

open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R216NonzeroNormalizedSqSurvivalConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Markov's inequality for a finite nonnegative spectrum, in count form. -/
theorem survival_count_le_of_moment_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) {θ B : ℝ} {r : ℕ}
    (hθ : 0 < θ) (hr : 1 ≤ r)
    (ht : ∀ b ∈ s, 0 ≤ t b)
    (hmoment : (∑ b ∈ s, (t b) ^ r) ≤ B * θ ^ r) :
    (((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤ B) := by
  have hθpow : 0 < θ ^ r := pow_pos hθ r
  have hpoint : ∀ b ∈ s.filter (fun b => θ ≤ t b), θ ^ r ≤ (t b) ^ r := by
    intro b hb
    have hbmem : b ∈ s := by simpa using (Finset.mem_filter.mp hb).1
    have hle : θ ≤ t b := by simpa using (Finset.mem_filter.mp hb).2
    exact pow_le_pow_left₀ hθ.le hle r
  have hcount_mul :
      ((s.filter (fun b => θ ≤ t b)).card : ℝ) * θ ^ r ≤
        ∑ b ∈ s.filter (fun b => θ ≤ t b), (t b) ^ r := by
    calc
      ((s.filter (fun b => θ ≤ t b)).card : ℝ) * θ ^ r
          = ∑ b ∈ s.filter (fun b => θ ≤ t b), θ ^ r := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ s.filter (fun b => θ ≤ t b), (t b) ^ r := Finset.sum_le_sum hpoint
  have hsub_le_full :
      (∑ b ∈ s.filter (fun b => θ ≤ t b), (t b) ^ r) ≤
        ∑ b ∈ s, (t b) ^ r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hxS _hxNot
      exact pow_nonneg (ht x hxS) r
  have hmain :
      ((s.filter (fun b => θ ≤ t b)).card : ℝ) * θ ^ r ≤ B * θ ^ r :=
    le_trans (le_trans hcount_mul hsub_le_full) hmoment
  exact le_of_mul_le_mul_right hmain hθpow

/-- Nonzero normalized-square grid tail from threshold-wise Markov moment
certificates. -/
theorem nonzeroNormalizedSqGridTail_of_moment_bounds
    (ψ : AddChar F ℂ) (G : Finset F) (σ : ℝ)
    (Θ : Finset ℝ) (rOf : ℝ → ℕ) (B : ℝ → ℝ)
    (hθpos : ∀ θ ∈ Θ, 0 < θ)
    (hr : ∀ θ ∈ Θ, 1 ≤ rOf θ)
    (hmoment : ∀ θ ∈ Θ,
      (∑ b ∈ nonzeroFreqs (F := F),
        (‖eta ψ G b‖ ^ 2 / σ ^ 2) ^ rOf θ) ≤ B θ * θ ^ rOf θ) :
    NonzeroNormalizedSqGridTail ψ G σ Θ B := by
  intro θ hθ
  exact survival_count_le_of_moment_bound
    (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2)
    (hθpos θ hθ) (hr θ hθ)
    (by intro b _; positivity)
    (hmoment θ hθ)

/-- End-to-end finite-grid Markov route to the R213 residual. -/
theorem nonzeroNormalizedSqQuarterMGFResidual_of_markov_moment_grid
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (Θ : Finset ℝ) (δ B : ℝ → ℝ) (rOf : ℝ → ℕ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ nonzeroFreqs (F := F),
      Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) ≤
        ∑ θ ∈ Θ.filter (fun θ => θ ≤ ‖eta ψ G b‖ ^ 2 / σ ^ 2), δ θ)
    (hθpos : ∀ θ ∈ Θ, 0 < θ)
    (hr : ∀ θ ∈ Θ, 1 ≤ rOf θ)
    (hmoment : ∀ θ ∈ Θ,
      (∑ b ∈ nonzeroFreqs (F := F),
        (‖eta ψ G b‖ ^ 2 / σ ^ 2) ^ rOf θ) ≤ B θ * θ ^ rOf θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * B θ)
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    NonzeroNormalizedSqQuarterMGFResidual ψ G σ := by
  exact nonzeroNormalizedSqQuarterMGFResidual_of_survival_count_ceiling
    ψ G Θ δ B hδ hstair
    (nonzeroNormalizedSqGridTail_of_moment_bounds ψ G σ Θ rOf B hθpos hr hmoment)
    hweighted

end ArkLib.ProximityGap.Frontier.R218MarkovMomentTailConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R218MarkovMomentTailConsumer.survival_count_le_of_moment_bound
#print axioms ArkLib.ProximityGap.Frontier.R218MarkovMomentTailConsumer.nonzeroNormalizedSqGridTail_of_moment_bounds
#print axioms ArkLib.ProximityGap.Frontier.R218MarkovMomentTailConsumer.nonzeroNormalizedSqQuarterMGFResidual_of_markov_moment_grid
