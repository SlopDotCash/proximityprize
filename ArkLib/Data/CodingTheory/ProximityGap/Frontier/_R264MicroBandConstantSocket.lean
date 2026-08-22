/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R264 micro-band constant socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# R264 (#466): micro-band constant socket

The current main-lane target is the direct micro-band count

```text
S(0.75) <= 612 / 1485.
```

R249 uses it only on the micro-band `[0.75, 0.755)`, where the required
half-rate constant is `0.6012`.  This file records the finite-carrier socket:
if the count cap and the numerical real inequality are supplied, then the
micro-band endpoint constant follows.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.R264MicroBandConstantSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- A direct cap at `τ`, plus the numerical endpoint inequality
`A exp(κ/2) <= C`, gives the R251 micro-band endpoint. -/
theorem microBandEndpoint_of_directCap
    (s : Finset ι) (t : ι → ℝ) {τ κ A C : ℝ}
    (hCap : DirectMicroBandCap s t τ A)
    (hNum : A * Real.exp (κ / 2) ≤ C) :
    SurvivorCount s t τ * Real.exp (κ / 2) ≤ C * (s.card : ℝ) := by
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
  have hexp_nonneg : 0 ≤ Real.exp (κ / 2) := le_of_lt (Real.exp_pos _)
  calc
    SurvivorCount s t τ * Real.exp (κ / 2)
        ≤ (A * (s.card : ℝ)) * Real.exp (κ / 2) := by
      exact mul_le_mul_of_nonneg_right hCap hexp_nonneg
    _ = (A * Real.exp (κ / 2)) * (s.card : ℝ) := by ring
    _ ≤ C * (s.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hNum hcard_nonneg

end

end ArkLib.ProximityGap.Frontier.R264MicroBandConstantSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R264MicroBandConstantSocket.microBandEndpoint_of_directCap
