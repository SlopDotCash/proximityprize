/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R28FMixedMomentGuards

/-!
# R29F (#466): calibrated consumers for the Main--Res mixed-moment socket

R27F isolates the live analytic input as two quantitative statements:

* `MixedMainResHalfCS S A B κ`, an improved Cauchy--Schwarz factor for
  `∑ A²B²`;
* `OddMainResBound S A B Θ`, a signed odd-moment allowance.

R28F records the basic monotonicity of those two sockets.  This file packages the
calibrated consumer shape used by the next analytic lanes: prove the mixed and odd
inputs at any sharper parameters `κ, Θ`, consume them against looser target
parameters `κ₀, Θ₀`, and check only the target budget inequality.

No strict mixed improvement is claimed here; the prize-facing content remains the
future proof of `κ < 1` and a small odd allowance for the concrete Main--Res pair.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated

open ArkLib.ProximityGap.Frontier.R27FMixedMoment
open ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards

section RealLayer

variable {ι : Type*}

/-- Calibrated real quartic consumer: sharper mixed/odd inputs may be spent at
looser target constants `κ₀, Θ₀`, so the final arithmetic check only mentions
the target constants. -/
theorem sum_quartic_le_of_mixed_half_cs_calibrated (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  exact le_trans
    (sum_quartic_le_of_mixed_half_cs (Ea := Ea) (Eb := Eb) (Θ := Θ₀) (κ := κ₀)
      S A B hκ0 hA hB
      (mixedMainResHalfCS_mono S A B hκκ₀ hM)
      (oddMainResBound_mono S A B hΘΘ₀ hO))
    hfit

/-- The common target used by the probes: a half-Cauchy mixed term and a calibrated
odd allowance. -/
theorem sum_quartic_le_of_mixed_half_target (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  refine sum_quartic_le_of_mixed_half_cs_calibrated (S := S) (A := A) (B := B)
    (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := 1 / 2)
    (Budget := Budget) ?_ hκ hΘΘ₀ hA hB hM hO ?_
  · norm_num
  · nlinarith [hfit]

/-- Deficit-form real consumer.  If the no-improvement Cauchy--Schwarz budget overspends
the desired budget by at most `Δ`, and the target mixed constant `κ₀` saves at least `Δ`
from the mixed term, then the calibrated quartic consumer fits the desired budget. -/
theorem sum_quartic_le_of_mixed_deficit (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget Δ : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hbase : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget + Δ)
    (hsave : Δ ≤ 6 * (1 - κ₀) * Real.sqrt (Ea * Eb)) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  refine sum_quartic_le_of_mixed_half_cs_calibrated (S := S) (A := A) (B := B)
    (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := κ₀)
    (Budget := Budget) hκ0 hκκ₀ hΘΘ₀ hA hB hM hO ?_
  nlinarith [hbase, hsave]

/-- Saved-budget real consumer.  This is the same algebra as
`sum_quartic_le_of_mixed_deficit`, but with the mixed-term saving subtracted directly
from the Cauchy--Schwarz baseline. -/
theorem sum_quartic_le_of_mixed_saved_budget (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 6 * (1 - κ₀) * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  refine sum_quartic_le_of_mixed_half_cs_calibrated (S := S) (A := A) (B := B)
    (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := κ₀)
    (Budget := Budget) hκ0 hκκ₀ hΘΘ₀ hA hB hM hO ?_
  nlinarith [hfit]

/-- Saving-rate real consumer.  If the mixed estimate is proved at
`κ ≤ 1 - σ`, then the Cauchy--Schwarz baseline may spend a direct
`6σ√(Ea·Eb)` saving. -/
theorem sum_quartic_le_of_mixed_saving_rate (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ σ Budget : ℝ}
    (_hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hκ : κ ≤ 1 - σ) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 6 * σ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  refine sum_quartic_le_of_mixed_saved_budget (S := S) (A := A) (B := B)
    (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := 1 - σ)
    (Budget := Budget) ?_ hκ hΘΘ₀ hA hB hM hO ?_
  · nlinarith [hσ1]
  · nlinarith [hfit]

/-- Half-saving real consumer, spelled in baseline-minus-saving form. -/
theorem sum_quartic_le_of_mixed_half_saving_budget (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 3 * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  exact sum_quartic_le_of_mixed_half_target S A B hκ hΘΘ₀ hA hB hM hO (by
    nlinarith [hfit])

/-- Real quartic consumer when the signed odd contribution is nonpositive.  This avoids
paying an absolute odd-moment allowance. -/
theorem sum_quartic_le_of_mixed_signed_odd_nonpos (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb κ Budget : ℝ} (hκ0 : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S A B κ)
    (hOdd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  have hA0 : (0 : ℝ) ≤ ∑ s ∈ S, (A s) ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ s ∈ S, (B s) ^ 4 :=
    Finset.sum_nonneg fun s _ => by positivity
  have hEa0 : (0 : ℝ) ≤ Ea := hA0.trans hA
  have hEb0 : (0 : ℝ) ≤ Eb := hB0.trans hB
  have hsqrt : Real.sqrt (∑ s ∈ S, (A s) ^ 4) * Real.sqrt (∑ s ∈ S, (B s) ^ 4)
      ≤ Real.sqrt (Ea * Eb) := by
    rw [Real.sqrt_mul hEa0]
    exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmix : ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2 ≤ κ * Real.sqrt (Ea * Eb) :=
    hM.trans (mul_le_mul_of_nonneg_left hsqrt hκ0)
  have hsplit : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3)
      = ∑ s ∈ S, (A s) ^ 3 * B s + ∑ s ∈ S, A s * (B s) ^ 3 :=
    Finset.sum_add_distrib
  rw [quartic_expansion]
  rw [hsplit] at hOdd
  have hodd4 : 4 * ∑ s ∈ S, (A s) ^ 3 * B s + 4 * ∑ s ∈ S, A s * (B s) ^ 3 ≤ 0 := by
    nlinarith
  have hmix6 : 6 * ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2 ≤
      6 * (κ * Real.sqrt (Ea * Eb)) := by
    nlinarith
  nlinarith [hA, hB, hmix6, hodd4, hfit]

end RealLayer

section ComplexBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Calibrated complex quartic consumer for the Main--Res bridge. -/
theorem sum_norm_quartic_le_of_mixed_faces_calibrated (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  exact sum_norm_quartic_le_of_mixed_faces (Ea := Ea) (Eb := Eb) (Θ := Θ₀) (κ := κ₀)
    S Mp Rv hMim hRim hκ0 hA hB
    (mixedMainResHalfCS_mono S (fun s => (Mp s).re) (fun s => (Rv s).re) hκκ₀ hM)
    (oddMainResBound_mono S (fun s => (Mp s).re) (fun s => (Rv s).re) hΘΘ₀ hO)
    hfit

/-- Complex bridge at the half-Cauchy mixed target. -/
theorem sum_norm_quartic_le_of_mixed_half_target (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  refine sum_norm_quartic_le_of_mixed_faces_calibrated (S := S) (Mp := Mp) (Rv := Rv)
    hMim hRim (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := 1 / 2)
    (Budget := Budget) ?_ hκ hΘΘ₀ hA hB hM hO ?_
  · norm_num
  · nlinarith [hfit]

/-- Deficit-form complex consumer for the Main--Res bridge. -/
theorem sum_norm_quartic_le_of_mixed_deficit (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget Δ : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hbase : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget + Δ)
    (hsave : Δ ≤ 6 * (1 - κ₀) * Real.sqrt (Ea * Eb)) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  refine sum_norm_quartic_le_of_mixed_faces_calibrated (S := S) (Mp := Mp) (Rv := Rv)
    hMim hRim (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := κ₀)
    (Budget := Budget) hκ0 hκκ₀ hΘΘ₀ hA hB hM hO ?_
  nlinarith [hbase, hsave]

/-- Saved-budget complex consumer for the Main--Res bridge. -/
theorem sum_norm_quartic_le_of_mixed_saved_budget (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0 : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 6 * (1 - κ₀) * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  refine sum_norm_quartic_le_of_mixed_faces_calibrated (S := S) (Mp := Mp) (Rv := Rv)
    hMim hRim (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ) (κ₀ := κ₀)
    (Budget := Budget) hκ0 hκκ₀ hΘΘ₀ hA hB hM hO ?_
  nlinarith [hfit]

/-- Saving-rate complex consumer for the Main--Res bridge. -/
theorem sum_norm_quartic_le_of_mixed_saving_rate (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ σ Budget : ℝ}
    (_hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hκ : κ ≤ 1 - σ) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 6 * σ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  refine sum_norm_quartic_le_of_mixed_saved_budget (S := S) (Mp := Mp) (Rv := Rv)
    hMim hRim (Ea := Ea) (Eb := Eb) (Θ := Θ) (Θ₀ := Θ₀) (κ := κ)
    (κ₀ := 1 - σ) (Budget := Budget) ?_ hκ hΘΘ₀ hA hB hM hO ?_
  · nlinarith [hσ1]
  · nlinarith [hfit]

/-- Half-saving complex consumer for the Main--Res bridge, spelled in
baseline-minus-saving form. -/
theorem sum_norm_quartic_le_of_mixed_half_saving_budget (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ₀
      - 3 * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  exact sum_norm_quartic_le_of_mixed_half_target S Mp Rv hMim hRim hκ hΘΘ₀ hA hB hM hO
    (by nlinarith [hfit])

/-- Complex Main--Res bridge when the signed odd contribution is nonpositive. -/
theorem sum_norm_quartic_le_of_mixed_signed_odd_nonpos (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb κ Budget : ℝ} (hκ0 : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hOdd : ∑ s ∈ S,
      (((Mp s).re) ^ 3 * (Rv s).re + (Mp s).re * ((Rv s).re) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  have hres : ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4
      = ∑ s ∈ S, ((Mp s).re + (Rv s).re) ^ 4 := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have him : (Mp s + Rv s).im = 0 := by
      rw [Complex.add_im, hMim s hs, hRim s hs, add_zero]
    rw [norm_pow_four_of_im_zero _ him, Complex.add_re]
  have hA' : ∑ s ∈ S, ((Mp s).re) ^ 4 ≤ Ea := by
    refine le_trans (le_of_eq ?_) hA
    exact Finset.sum_congr rfl fun s hs =>
      (norm_pow_four_of_im_zero _ (hMim s hs)).symm
  have hB' : ∑ s ∈ S, ((Rv s).re) ^ 4 ≤ Eb := by
    refine le_trans (le_of_eq ?_) hB
    exact Finset.sum_congr rfl fun s hs =>
      (norm_pow_four_of_im_zero _ (hRim s hs)).symm
  rw [hres]
  exact sum_quartic_le_of_mixed_signed_odd_nonpos S
    (fun s => (Mp s).re) (fun s => (Rv s).re) hκ0 hA' hB' hM hOdd hfit

end ComplexBridge

end ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_half_cs_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_half_target
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_deficit
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_saved_budget
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_saving_rate
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_half_saving_budget
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_quartic_le_of_mixed_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_faces_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_half_target
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_deficit
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_saved_budget
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_saving_rate
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_half_saving_budget
#print axioms ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated.sum_norm_quartic_le_of_mixed_signed_odd_nonpos
