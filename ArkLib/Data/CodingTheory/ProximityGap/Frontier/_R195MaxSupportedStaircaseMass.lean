/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R195 max-supported staircase mass)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R193SpikeMassBudgetConsumer

/-!
# R195 (#466): max-supported staircase mass

R194 points at a logarithmic max bound.  R193 consumes a scalar staircase-mass
bound.  This file connects those two in the finite-grid setting: if the
staircase increments are supported only up to a threshold `Tmax`, then the
total staircase mass is just the prefix mass below `Tmax`.

This is the Lean-facing bookkeeping needed for a later concrete half-grid
certificate:

```text
  max_i t_i ≤ Tmax
  δ(θ) = 0 for θ > Tmax
  Σ_{θ≤Tmax} δ(θ) ≤ M
  --------------------------------
  StaircaseMass Θ δ ≤ M.
```

Status: consumer only.  Residual = instantiate `δ` for the R189 half-grid and
prove the prefix geometric/telescoping bound from the logarithmic max estimate.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R195MaxSupportedStaircaseMass

open ArkLib.ProximityGap.Frontier.R193SpikeMassBudgetConsumer

noncomputable section

/-- The staircase increments have no mass above `Tmax` on the chosen grid. -/
def MaxSupportedStaircase (Θ : Finset ℝ) (δ : ℝ → ℝ) (Tmax : ℝ) : Prop :=
  ∀ θ ∈ Θ, Tmax < θ → δ θ = 0

/-- If a staircase is supported below `Tmax`, its total mass equals its prefix
mass on thresholds `θ ≤ Tmax`. -/
theorem staircaseMass_eq_prefix_of_maxSupported
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Tmax : ℝ)
    (hSupport : MaxSupportedStaircase Θ δ Tmax) :
    StaircaseMass Θ δ =
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ Tmax), δ θ := by
  unfold StaircaseMass
  rw [← Finset.sum_filter_add_sum_filter_not Θ (fun θ => θ ≤ Tmax) δ]
  have hzero : (∑ θ ∈ Θ.filter (fun θ => ¬ θ ≤ Tmax), δ θ) = 0 := by
    apply Finset.sum_eq_zero
    intro θ hθ
    have hθΘ : θ ∈ Θ := (Finset.mem_filter.mp hθ).1
    have hnot : ¬ θ ≤ Tmax := (Finset.mem_filter.mp hθ).2
    have hlt : Tmax < θ := lt_of_not_ge hnot
    exact hSupport θ hθΘ hlt
  rw [hzero, add_zero]

/-- Prefix mass control proves the total staircase-mass ceiling consumed by
R193. -/
theorem staircaseMass_le_of_maxSupported_prefix
    (Θ : Finset ℝ) (δ : ℝ → ℝ) (Tmax M : ℝ)
    (hSupport : MaxSupportedStaircase Θ δ Tmax)
    (hPrefix : (∑ θ ∈ Θ.filter (fun θ => θ ≤ Tmax), δ θ) ≤ M) :
    StaircaseMass Θ δ ≤ M := by
  rw [staircaseMass_eq_prefix_of_maxSupported Θ δ Tmax hSupport]
  exact hPrefix

end

end ArkLib.ProximityGap.Frontier.R195MaxSupportedStaircaseMass

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R195MaxSupportedStaircaseMass.staircaseMass_eq_prefix_of_maxSupported
#print axioms ArkLib.ProximityGap.Frontier.R195MaxSupportedStaircaseMass.staircaseMass_le_of_maxSupported_prefix
