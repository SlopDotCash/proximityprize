/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FMixedMoment

/-!
# R28F (#466): monotone guards around the Main--Res mixed-moment socket

R27F isolates the live mixed Main--Res input as a `κ`-improved Cauchy--Schwarz bound plus
an odd signed-moment bound.  This file records the basic order structure around that socket:

* `MixedMainResHalfCS` is monotone in `κ`;
* `OddMainResBound` is monotone in `Θ`;
* the unconditional Cauchy--Schwarz face is exactly the baseline case `κ = 1`;
* therefore the R27F complex quartic consumer has a baseline `κ = 1` form.

The prize-facing content remains the strict improvement `κ < 1` with a small odd term.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards

open ArkLib.ProximityGap.Frontier.R27FMixedMoment

section RealLayer

variable {ι : Type*}

/-- The `κ`-improved mixed bound is monotone in `κ`. -/
theorem mixedMainResHalfCS_mono (S : Finset ι) (A B : ι → ℝ) {κ κ' : ℝ}
    (hκκ' : κ ≤ κ') (hM : MixedMainResHalfCS S A B κ) :
    MixedMainResHalfCS S A B κ' := by
  have hP : 0 ≤ Real.sqrt (∑ s ∈ S, (A s) ^ 4) *
      Real.sqrt (∑ s ∈ S, (B s) ^ 4) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hM.trans (mul_le_mul_of_nonneg_right hκκ' hP)

/-- The signed odd-moment bound is monotone in the permitted allowance `Θ`. -/
theorem oddMainResBound_mono (S : Finset ι) (A B : ι → ℝ) {Θ Θ' : ℝ}
    (hΘΘ' : Θ ≤ Θ') (hO : OddMainResBound S A B Θ) :
    OddMainResBound S A B Θ' :=
  hO.trans hΘΘ'

/-- The un-improved Cauchy--Schwarz face is exactly the `κ = 1` mixed bound. -/
theorem mixedMainResHalfCS_one (S : Finset ι) (A B : ι → ℝ) :
    MixedMainResHalfCS S A B 1 := by
  simpa [MixedMainResHalfCS] using mixed_sq_le_sqrt_quartics S A B

/-- Any `κ ≥ 1` version of the mixed socket is automatic from Cauchy--Schwarz. -/
theorem mixedMainResHalfCS_of_one_le (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hκ : 1 ≤ κ) :
    MixedMainResHalfCS S A B κ :=
  mixedMainResHalfCS_mono S A B hκ (mixedMainResHalfCS_one S A B)

/-- Baseline real quartic bookkeeping with the mixed term bounded only by Cauchy--Schwarz. -/
theorem sum_quartic_le_of_cs_and_odd (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Budget : ℝ}
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget := by
  exact le_trans
    (sum_quartic_le_of_mixed_half_cs (Ea := Ea) (Eb := Eb) (Θ := Θ) (κ := 1)
      S A B (by norm_num) hA hB (mixedMainResHalfCS_one S A B) hO)
    (by simpa [one_mul] using hfit)

end RealLayer

section ComplexBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Baseline complex quartic consumer using only Cauchy--Schwarz for the mixed term. -/
theorem sum_norm_quartic_le_of_cs_and_odd (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Budget : ℝ}
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * Real.sqrt (Ea * Eb) + 4 * Θ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget := by
  exact sum_norm_quartic_le_of_mixed_faces (Ea := Ea) (Eb := Eb) (Θ := Θ) (κ := 1)
    S Mp Rv hMim hRim (by norm_num) hA hB
    (mixedMainResHalfCS_one S (fun s => (Mp s).re) (fun s => (Rv s).re)) hO
    (by simpa [one_mul] using hfit)

end ComplexBridge

end ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.mixedMainResHalfCS_mono
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.oddMainResBound_mono
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.mixedMainResHalfCS_one
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.mixedMainResHalfCS_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.sum_quartic_le_of_cs_and_odd
#print axioms ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards.sum_norm_quartic_le_of_cs_and_odd
