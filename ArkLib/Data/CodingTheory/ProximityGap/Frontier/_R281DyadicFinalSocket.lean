/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R281 dyadic final socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R281 (#466): dyadic final micro-band socket

R281 certifies the bridge `8001 <= M < 8192`, so the final branch split is:

* finite certificates for `M < 8192`;
* a stronger asymptotic cap for `8192 <= M`.

This socket records that a strong asymptotic cap constant, such as `0.394`,
implies the weaker required cap constant, such as `0.404`.
-/

namespace ArkLib.ProximityGap.Frontier.R281DyadicFinalSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- Finite coverage below `8192` plus a stronger asymptotic cap above `8192`
implies the weaker direct cap at every index. -/
theorem directMicroBandCap_of_finite_lt8192_and_strong_asymptotic
    (s : Finset ι) (t : ι → ℝ) (τ Astrong Aweak : ℝ) (M : ℕ)
    (hStrongWeak : Astrong ≤ Aweak)
    (hFinite : M < 8192 → DirectMicroBandCap s t τ Aweak)
    (hAsymp : 8192 ≤ M → DirectMicroBandCap s t τ Astrong) :
    DirectMicroBandCap s t τ Aweak := by
  by_cases hM : M < 8192
  · exact hFinite hM
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
  exact le_trans (hAsymp (Nat.le_of_not_gt hM))
    (mul_le_mul_of_nonneg_right hStrongWeak hcard_nonneg)

end

end ArkLib.ProximityGap.Frontier.R281DyadicFinalSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R281DyadicFinalSocket.directMicroBandCap_of_finite_lt8192_and_strong_asymptotic
