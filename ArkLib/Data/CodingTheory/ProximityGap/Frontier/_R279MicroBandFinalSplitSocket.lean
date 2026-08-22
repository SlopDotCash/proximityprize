/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R279 final micro-band split socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R279 (#466): final micro-band split socket

R278 extends the finite CSV certificate coverage to `2048 <= M <= 8000`.
This file records the exact propositional split now needed for the trim-five
micro-band endpoint:

* `512 <= M < 1536`  -- R269/R270 finite certificate;
* `1536 <= M < 2048` -- R275/R270 finite certificate;
* `2048 <= M < 8001` -- R278/R270 finite certificate;
* `8001 <= M`        -- remaining asymptotic theorem.

The socket intentionally does not encode the CSV verifier.  It only proves that
these four branch obligations are sufficient for the direct cap.
-/

namespace ArkLib.ProximityGap.Frontier.R279MicroBandFinalSplitSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- The final R278 split: three finite windows plus the `M >= 8001` asymptotic branch. -/
theorem directMicroBandCap_of_threeFiniteWindows_and_asymptotic
    (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) (M : ℕ)
    (hA : M < 1536 → DirectMicroBandCap s t τ A)
    (hB : 1536 ≤ M → M < 2048 → DirectMicroBandCap s t τ A)
    (hC : 2048 ≤ M → M < 8001 → DirectMicroBandCap s t τ A)
    (hD : 8001 ≤ M → DirectMicroBandCap s t τ A) :
    DirectMicroBandCap s t τ A := by
  by_cases hM1536 : M < 1536
  · exact hA hM1536
  have h1536 : 1536 ≤ M := Nat.le_of_not_gt hM1536
  by_cases hM2048 : M < 2048
  · exact hB h1536 hM2048
  have h2048 : 2048 ≤ M := Nat.le_of_not_gt hM2048
  by_cases hM8001 : M < 8001
  · exact hC h2048 hM8001
  exact hD (Nat.le_of_not_gt hM8001)

end

end ArkLib.ProximityGap.Frontier.R279MicroBandFinalSplitSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R279MicroBandFinalSplitSocket.directMicroBandCap_of_threeFiniteWindows_and_asymptotic
