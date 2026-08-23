/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R211 nonzero normalized-square dilation consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R207NonzeroGaussPeriodDilationConsumer

/-!
# R211 (#466): nonzero normalized-square Gauss-period dilation consumer

R207 removed the principal/DC frequency from the concrete dilation bridge, but
phrased the one-child residual in raw norms.  The numeric stress probes and the
standard variance-normalized prize surface use the squared normalized spectrum

```text
X_G(b) = ‖η_G(b)‖^2 / σ^2.
```

This file records the corrected deterministic bridge on the nonzero carrier:
the triangle recursion plus Cauchy's inequality gives

```text
X_{G∪ζG}(b) ≤ X_G(b) + X_G(ζ b)
```

when the parent variance denominator is `2σ²`.  Thus the remaining analytic
residual is the nonzero one-child quarter-MGF bound for the normalized-square
spectrum, matching the probes rather than the over-strong raw-norm target.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Normalized-square Cauchy step for one concrete Gauss-period dilation. -/
theorem normalizedSq_eta_union_dilate_le_child_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ) (b : F) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2) ≤
      ‖eta ψ G b‖ ^ 2 / σ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2 := by
  set p := ‖eta ψ (G ∪ dilate ζ G) b‖ with hp
  set x := ‖eta ψ G b‖ with hx
  set y := ‖eta ψ G (ζ * b)‖ with hy
  have hp_nonneg : 0 ≤ p := by simp [hp]
  have hx_nonneg : 0 ≤ x := by simp [hx]
  have hy_nonneg : 0 ≤ y := by simp [hy]
  have htri : p ≤ x + y := by
    simpa [hp, hx, hy] using eta_union_dilate_norm_le ψ G hζ hdisj b
  have hsq_tri : p ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x + y - p)]
  have hσsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hden : 0 < 2 * σ ^ 2 := by nlinarith
  have hmain : p ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have hcs : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
    nlinarith
  calc
    p ^ 2 / (2 * σ ^ 2)
        ≤ (2 * (x ^ 2 + y ^ 2)) / (2 * σ ^ 2) := div_le_div_of_nonneg_right hmain hden.le
    _ = x ^ 2 / σ ^ 2 + y ^ 2 / σ ^ 2 := by field_simp [hσsq.ne']

/-- The normalized-square quarter-MGF sum over nonzero frequencies is invariant
under a nonzero multiplicative frequency shift. -/
theorem nonzero_quarter_sum_normalizedSq_eta_shift_eq
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ} (hζ : ζ ≠ 0) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2)))
      = ∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) := by
  refine Finset.sum_nbij' (fun b : F => ζ * b) (fun c : F => ζ⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact mul_mem_nonzeroFreqs hζ hb
  · intro c hc
    exact mul_mem_nonzeroFreqs (inv_ne_zero hζ) hc
  · intro b _
    simp [hζ]
  · intro c _
    field_simp [hζ]
  · intro _ _
    rfl

/-- Inequality form of the nonzero normalized-square shift identity. -/
theorem nonzero_quarter_sum_normalizedSq_eta_shift_le
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ} (hζ : ζ ≠ 0) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2)))
      ≤ ∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)) :=
  (nonzero_quarter_sum_normalizedSq_eta_shift_eq ψ G (σ := σ) hζ).le

/-- Nonzero-frequency dyadic-tail MGF residual for the normalized-square
dilation parent. -/
theorem dyadicTailMGF_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    (hLeft :
      (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    DyadicTailMGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) := by
  refine dyadicTailMGF_of_shifted_quarter (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2))
    (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2)
    (fun b => ‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2) ?_ ?_ hLeft
  · intro b _
    exact normalizedSq_eta_union_dilate_le_child_sum ψ G hζ hdisj hσ b
  · exact nonzero_quarter_sum_normalizedSq_eta_shift_le ψ G (σ := σ) hζ

/-- Prize-square endpoint for the normalized nonprincipal dilation spectrum. -/
theorem prize_sq_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft :
      (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * (‖eta ψ G b‖ ^ 2 / σ ^ 2)))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_shifted_quarter (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2))
    (fun b => ‖eta ψ G b‖ ^ 2 / σ ^ 2)
    (fun b => ‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2) ?_ ?_ hLeft
    hMmax hn hQ ?_ hP hr hrQ ?_
  · intro b _
    exact normalizedSq_eta_union_dilate_le_child_sum ψ G hζ hdisj hσ b
  · exact nonzero_quarter_sum_normalizedSq_eta_shift_le ψ G (σ := σ) hζ
  · intro b _
    positivity
  · exact hmoment

end ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer.normalizedSq_eta_union_dilate_le_child_sum
#print axioms ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer.nonzero_quarter_sum_normalizedSq_eta_shift_eq
#print axioms ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer.dyadicTailMGF_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
#print axioms ArkLib.ProximityGap.Frontier.R211NonzeroNormalizedSqDilationConsumer.prize_sq_of_nonzero_normalizedSq_gaussPeriod_dilation_quarter
