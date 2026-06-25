/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Incidence smoothing must pay its deconvolution norm

This scratch frontier file records a small obstruction for the tempting route:

1. smooth the bad-scalar / offset-incidence profile;
2. prove a good bound for the smoothed profile;
3. recover the raw worst-case incidence by deconvolution.

The point is bookkeeping, not a new analytic estimate.  If the recovery step has inverse
amplification `R`, then a smoothed bound `B` certifies only the raw bound `R * B`.  To certify a
target `T`, the smoothed theorem must beat the target by the same inverse factor.  A lossy filter
with a killed mode is worse: it can make the smoothed norm zero while the raw worst-case component
is still above target, unless one proves extra structure excluding that component.

This is the deconvolution analogue of the Door-IV gauge barrier.  It does not prove the prize floor
or any Paley/BGK cancellation theorem; it only says where a smoothing proof has to spend its norm.
-/

namespace ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier

/-- **Deconvolution pays the inverse norm.**  If a raw worst-case quantity is recovered from a
smoothed quantity with amplification `R`, then a smoothed budget `B` certifies only the raw budget
`R * B`. -/
theorem deconvolution_bound_pays_inverse_norm
    {raw smooth R B : ℝ} (hR : 0 ≤ R)
    (hinv : raw ≤ R * smooth) (hsmooth : smooth ≤ B) :
    raw ≤ R * B := by
  exact le_trans hinv (mul_le_mul_of_nonneg_left hsmooth hR)

/-- **A target proof needs the inverse-loss budget.**  If `R * B <= T`, then a smoothed bound
`smooth <= B`, together with the deconvolution inequality `raw <= R * smooth`, proves `raw <= T`.
The price of smoothing is therefore the explicit `R` in the budget. -/
theorem target_bound_of_deconvolution_budget
    {raw smooth R B T : ℝ} (hR : 0 ≤ R)
    (hinv : raw ≤ R * smooth) (hsmooth : smooth ≤ B)
    (hbudget : R * B ≤ T) :
    raw ≤ T :=
  le_trans (deconvolution_bound_pays_inverse_norm hR hinv hsmooth) hbudget

/-- **Contrapositive diagnostic.**  If the raw profile actually exceeds a target `T`, then every
valid smoothing/deconvolution certificate must have `T < R * B`.  Thus a proof with
`R * B <= T` cannot be compatible with such a raw spike. -/
theorem exceeded_target_forces_inverse_loss_budget
    {raw smooth R B T : ℝ} (hR : 0 ≤ R)
    (hinv : raw ≤ R * smooth) (hsmooth : smooth ≤ B)
    (hraw : T < raw) :
    T < R * B :=
  lt_of_lt_of_le hraw (deconvolution_bound_pays_inverse_norm hR hinv hsmooth)

/-- **No raw spike can survive a sufficient deconvolution budget.**  This is the same diagnostic in
negated form: once `R * B <= T` is available, a raw counterexample `T < raw` is impossible. -/
theorem no_exceeded_target_under_deconvolution_budget
    {raw smooth R B T : ℝ} (hR : 0 ≤ R)
    (hinv : raw ≤ R * smooth) (hsmooth : smooth ≤ B)
    (hbudget : R * B ≤ T) :
    ¬ T < raw := by
  intro hraw
  exact (not_lt_of_ge (target_bound_of_deconvolution_budget hR hinv hsmooth hbudget)) hraw

/-- **A small multiplier forces a large inverse product.**  On a Fourier mode where the smoothing
multiplier has size at most `a`, any left-inverse certificate on that mode has to satisfy
`1 <= R * a`.  This is the multiplication-form version of the usual reciprocal loss
`R >= 1 / a`; it avoids committing this abstract file to a particular Fourier normalization. -/
theorem small_multiplier_forces_inverse_product
    {R m a : ℝ} (hR : 0 ≤ R) (hm : m ≤ a)
    (hleft : 1 ≤ R * m) :
    1 ≤ R * a :=
  le_trans hleft (mul_le_mul_of_nonneg_left hm hR)

/-- **Killed modes block finite deconvolution.**  If the smoothed quantity is zero on a component
but the raw quantity is strictly positive there, no finite inequality of the form
`raw <= R * smooth` can hold.  This models a low-pass or lossy smoother on a worst-case mode. -/
theorem killed_mode_blocks_finite_deconvolution
    {raw smooth R : ℝ} (hsmooth : smooth = 0) (hraw : 0 < raw) :
    ¬ raw ≤ R * smooth := by
  intro hinv
  rw [hsmooth, mul_zero] at hinv
  exact (not_lt_of_ge hinv) hraw

/-- **Kernel blindness witness.**  A killed component can satisfy any nonnegative smoothed budget
while still violating an arbitrary raw target.  A smoothing proof must therefore either keep an
invertible multiplier on every prize-relevant mode or add a separate structural theorem excluding
such raw components. -/
theorem killed_mode_can_pass_any_nonnegative_smooth_budget
    {raw smooth B T : ℝ} (hB : 0 ≤ B)
    (hsmooth : smooth = 0) (hraw : T < raw) :
    smooth ≤ B ∧ T < raw := by
  exact ⟨by rw [hsmooth]; exact hB, hraw⟩

end ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier

#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.deconvolution_bound_pays_inverse_norm
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.target_bound_of_deconvolution_budget
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.exceeded_target_forces_inverse_loss_budget
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.no_exceeded_target_under_deconvolution_budget
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.small_multiplier_forces_inverse_product
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.killed_mode_blocks_finite_deconvolution
#print axioms ArkLib.ProximityGap.Frontier.IncidenceSmoothingDeconvolutionBarrier.killed_mode_can_pass_any_nonnegative_smooth_budget
