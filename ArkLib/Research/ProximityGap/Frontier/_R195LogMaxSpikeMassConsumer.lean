/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R195 log-max spike mass consumer)
-/
import Mathlib

/-!
# R195 (#466): log-max control of spike staircase mass

R194 probes the scalar spike-mass side of the bulk/spike quarter-MGF route.
The practical sufficient condition is:

```text
  Kspike * StaircaseMass <= Bspike * M.
```

For the half-grid staircase used by the probes, `StaircaseMass` is controlled
by `exp(Xmax/4)`.  Hence a logarithmic max bound

```text
  exp(Xmax/4) / M <= Bspike / Kspike
```

closes the spike side.  This file proves only that deterministic reduction.
The analytic content remains the actual finite-field max-period/log law.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R195LogMaxSpikeMassConsumer

/-- Total mass of a finite threshold staircase. -/
def StaircaseMass (Θ : Finset ℝ) (δ : ℝ → ℝ) : ℝ :=
  ∑ θ ∈ Θ, δ θ

/-- If the staircase mass is bounded by `exp(Xmax/4)` and the logarithmic
max-spike ratio is inside budget, then the spike weighted budget closes. -/
theorem spike_mass_budget_of_expMax_ratio
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {Xmax M Kspike Bspike : ℝ}
    (hMass : StaircaseMass Θ δ ≤ Real.exp ((1 / 4 : ℝ) * Xmax))
    (hRatio : Kspike * Real.exp ((1 / 4 : ℝ) * Xmax) ≤ Bspike * M)
    (hK : 0 ≤ Kspike) :
    Kspike * StaircaseMass Θ δ ≤ Bspike * M := by
  exact (mul_le_mul_of_nonneg_left hMass hK).trans hRatio

/-- Logarithmic max form.  A bound
`Xmax <= 4 * log (Bspike*M/Kspike)` implies the exponential-ratio budget,
assuming the logarithm argument is positive.

This is the literal R194 target, separated from the staircase-mass certificate. -/
theorem expMax_ratio_of_log_bound
    {Xmax M Kspike Bspike : ℝ}
    (hpos : 0 < Bspike * M / Kspike)
    (hX : Xmax ≤ 4 * Real.log (Bspike * M / Kspike)) :
    Real.exp ((1 / 4 : ℝ) * Xmax) ≤ Bspike * M / Kspike := by
  have hquarter : (1 / 4 : ℝ) * Xmax ≤ Real.log (Bspike * M / Kspike) := by
    nlinarith
  exact (Real.exp_le_exp.mpr hquarter).trans_eq (Real.exp_log hpos)

/-- Combined log-max spike-budget consumer. -/
theorem spike_mass_budget_of_log_bound
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {Xmax M Kspike Bspike : ℝ}
    (hMass : StaircaseMass Θ δ ≤ Real.exp ((1 / 4 : ℝ) * Xmax))
    (hpos : 0 < Bspike * M / Kspike)
    (hX : Xmax ≤ 4 * Real.log (Bspike * M / Kspike))
    (hK : 0 < Kspike) :
    Kspike * StaircaseMass Θ δ ≤ Bspike * M := by
  have hratio_div := expMax_ratio_of_log_bound (Xmax := Xmax)
    (M := M) (Kspike := Kspike) (Bspike := Bspike) hpos hX
  have hratio : Kspike * Real.exp ((1 / 4 : ℝ) * Xmax) ≤ Bspike * M := by
    have := mul_le_mul_of_nonneg_left hratio_div (le_of_lt hK)
    field_simp [ne_of_gt hK] at this
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  exact spike_mass_budget_of_expMax_ratio Θ δ hMass hratio (le_of_lt hK)

end ArkLib.ProximityGap.Frontier.R195LogMaxSpikeMassConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R195LogMaxSpikeMassConsumer.spike_mass_budget_of_expMax_ratio
#print axioms ArkLib.ProximityGap.Frontier.R195LogMaxSpikeMassConsumer.expMax_ratio_of_log_bound
#print axioms ArkLib.ProximityGap.Frontier.R195LogMaxSpikeMassConsumer.spike_mass_budget_of_log_bound
