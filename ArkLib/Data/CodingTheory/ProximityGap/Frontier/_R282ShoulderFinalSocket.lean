/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R282 shoulder final socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R282 (#466): shoulder-adjusted final micro-band socket

Exact enumeration refutes the speculative R280 cap `M >= 8192 => S(0.75) <= 0.394`.
R282 certifies the near-dyadic shoulder `8192 <= M <= 10000`, leaving the final
analytic branch at `10001 <= M`.
-/

namespace ArkLib.ProximityGap.Frontier.R282ShoulderFinalSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- Finite coverage below `10001` plus a strong asymptotic cap from `10001`
onward implies the weaker required direct cap. -/
theorem directMicroBandCap_of_finite_lt10001_and_strong_asymptotic
    (s : Finset ι) (t : ι → ℝ) (τ Astrong Aweak : ℝ) (M : ℕ)
    (hStrongWeak : Astrong ≤ Aweak)
    (hFinite : M < 10001 → DirectMicroBandCap s t τ Aweak)
    (hAsymp : 10001 ≤ M → DirectMicroBandCap s t τ Astrong) :
    DirectMicroBandCap s t τ Aweak := by
  by_cases hM : M < 10001
  · exact hFinite hM
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
  exact le_trans (hAsymp (Nat.le_of_not_gt hM))
    (mul_le_mul_of_nonneg_right hStrongWeak hcard_nonneg)

end

end ArkLib.ProximityGap.Frontier.R282ShoulderFinalSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R282ShoulderFinalSocket.directMicroBandCap_of_finite_lt10001_and_strong_asymptotic
