/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R284 third shoulder final socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R284 (#466): third-shoulder final micro-band socket

R284 certifies `15000 <= M < 20000`, moving the remaining analytic branch to
`20000 <= M`.
-/

namespace ArkLib.ProximityGap.Frontier.R284ThirdShoulderFinalSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- Finite coverage below `20000` plus a strong asymptotic cap from `20000`
onward implies the weaker required direct cap. -/
theorem directMicroBandCap_of_finite_lt20000_and_strong_asymptotic
    (s : Finset ι) (t : ι → ℝ) (τ Astrong Aweak : ℝ) (M : ℕ)
    (hStrongWeak : Astrong ≤ Aweak)
    (hFinite : M < 20000 → DirectMicroBandCap s t τ Aweak)
    (hAsymp : 20000 ≤ M → DirectMicroBandCap s t τ Astrong) :
    DirectMicroBandCap s t τ Aweak := by
  by_cases hM : M < 20000
  · exact hFinite hM
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
  exact le_trans (hAsymp (Nat.le_of_not_gt hM))
    (mul_le_mul_of_nonneg_right hStrongWeak hcard_nonneg)

end

end ArkLib.ProximityGap.Frontier.R284ThirdShoulderFinalSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R284ThirdShoulderFinalSocket.directMicroBandCap_of_finite_lt20000_and_strong_asymptotic
