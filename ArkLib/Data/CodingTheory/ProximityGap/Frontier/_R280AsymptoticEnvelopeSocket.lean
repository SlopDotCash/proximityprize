/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R280 asymptotic envelope socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R280 (#466): asymptotic envelope socket

R280 proposes a stronger large-index theorem:

```text
M >= 8192 => S(0.75) <= 0.394
```

Since `0.394 <= 0.404`, this is enough for the remaining micro-band branch,
modulo a tiny finite bridge `8001 <= M < 8192`.  This file records that
accounting in the same finite-carrier language as R279.
-/

namespace ArkLib.ProximityGap.Frontier.R280AsymptoticEnvelopeSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- A stronger cap constant implies a weaker cap constant. -/
theorem directMicroBandCap_mono_const
    (s : Finset ι) (t : ι → ℝ) (τ : ℝ) {A B : ℝ}
    (hAB : A ≤ B) (hA : DirectMicroBandCap s t τ A) :
    DirectMicroBandCap s t τ B := by
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
  exact le_trans hA (mul_le_mul_of_nonneg_right hAB hcard_nonneg)

/-- R280 branch accounting: finite through `8000`, tiny bridge through `8191`,
then the stronger asymptotic envelope from `8192` onward. -/
theorem directMicroBandCap_of_finite_bridge_and_stronger_asymptotic
    (s : Finset ι) (t : ι → ℝ) (τ Astrong Aweak : ℝ) (M : ℕ)
    (hStrongWeak : Astrong ≤ Aweak)
    (hFinite : M < 8001 → DirectMicroBandCap s t τ Aweak)
    (hBridge : 8001 ≤ M → M < 8192 → DirectMicroBandCap s t τ Aweak)
    (hAsymp : 8192 ≤ M → DirectMicroBandCap s t τ Astrong) :
    DirectMicroBandCap s t τ Aweak := by
  by_cases hM8001 : M < 8001
  · exact hFinite hM8001
  have h8001 : 8001 ≤ M := Nat.le_of_not_gt hM8001
  by_cases hM8192 : M < 8192
  · exact hBridge h8001 hM8192
  exact directMicroBandCap_mono_const s t τ hStrongWeak (hAsymp (Nat.le_of_not_gt hM8192))

end

end ArkLib.ProximityGap.Frontier.R280AsymptoticEnvelopeSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R280AsymptoticEnvelopeSocket.directMicroBandCap_mono_const
#print axioms
  ArkLib.ProximityGap.Frontier.R280AsymptoticEnvelopeSocket.directMicroBandCap_of_finite_bridge_and_stronger_asymptotic
