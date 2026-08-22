/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCMeanFloorSharp

/-!
# The off-DC peak floor against the SHARP closed-form floor (#444 door-iv)

Two proven substrate rungs were landed separately on the concrete order-`d` subgroup indicator
`1_{μ_d}` (`d ∣ N`), but never composed:

* `_DoorIVSubgroupOffDCPeakFloor.exists_offDC_peak_sq_ge_mean`:
  the off-DC PEAK² is at least the exact off-DC MEAN energy,
  `max_{k≠0} ‖𝓕 1_{μ_d} k‖² ≥ (N·d − d²)/(N − 1)`.
* `_DoorIVSubgroupOffDCMeanFloorSharp.subgroupIndicator_offDC_mean_ge`:
  that exact off-DC mean energy is at least the SHARP closed form
  `(N·d − d²)/(N − 1) ≥ d·(1 − (d − 1)/(N − 1))`.

This file composes the two by transitivity to floor the prize object `M(μ_n)` DIRECTLY against the
sharp `d·(1 − o(1))` closed form, rather than against the raw quotient `(N·d − d²)/(N − 1)`:
```
        max_{k≠0} ‖𝓕 1_{μ_d} k‖²  ≥  d·(1 − (d − 1)/(N − 1)).
```
In the prize regime `N = q ≈ d^β` (`β ≈ 4-5`) the relative defect `(d − 1)/(N − 1) ≈ d^{1−β} → 0`,
so the floor is `d·(1 − o(1))` and the norm floor is `M(μ_n) ≥ √d·(1 − o(1)) = √n·(1 − o(1))` — the
honest Plancherel `√n` floor on the *correct off-DC object*, now stated against the SHARP form that
makes the `o(1)` convergence to `√n` explicit (no need to pass through the unfactored quotient).

* `exists_offDC_peak_sq_ge_sharpFloor` : ∃ argmax `k₀ ≠ 0` with
  `d·(1 − (d − 1)/(N − 1)) ≤ ‖𝓕 1_{μ_d} k₀‖²`.
* `exists_offDC_peak_ge_sqrt_sharpFloor` : the norm form,
  `√(d·(1 − (d − 1)/(N − 1))) ≤ ‖𝓕 1_{μ_d} k₀‖`.

NOTE on scope: this is the same FLOOR (lower bound) on the off-DC peak as the companion — the EASY
direction, the lower endpoint of the Shaw bracket — only re-expressed against the sharp closed form
`d·(1 − (d − 1)/(N − 1))` so the `→ d` (i.e. `→ √n`) behaviour is visible without unfolding the
quotient.  It does NOT touch the OPEN CORE upper bound `M(μ_n) ≤ C·√(n·log(p/n))`.  No cancellation,
completion, anti-concentration, moment-saving, or capacity claim.  CORE remains OPEN; door (iv)
remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor
open ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- **Off-DC peak² ≥ sharp closed-form floor.**  Composing the off-DC peak floor
`max_{k≠0} ‖𝓕 1_{μ_d} k‖² ≥ (N·d − d²)/(N − 1)` with the sharp mean lower bound
`(N·d − d²)/(N − 1) ≥ d·(1 − (d − 1)/(N − 1))`, the off-DC peak squared is at least the sharp
closed form `d·(1 − (d − 1)/(N − 1))`.  This re-expresses the same Plancherel floor against the
factored form whose `→ d` limit (relative defect `(d − 1)/(N − 1) → 0`) is explicit. -/
theorem exists_offDC_peak_sq_ge_sharpFloor {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
        ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 := by
  obtain ⟨k₀, hk₀mem, hk₀⟩ := exists_offDC_peak_sq_ge_mean hd hN1
  refine ⟨k₀, hk₀mem, ?_⟩
  exact le_trans (subgroupIndicator_offDC_mean_ge hN1) hk₀

/-- **Off-DC peak floor against the sharp closed form (norm form).**  There is an off-DC frequency
`k₀ ≠ 0` whose DFT magnitude is at least the square root of the sharp closed-form floor:
`‖𝓕 1_{μ_d} k₀‖ ≥ √(d·(1 − (d − 1)/(N − 1)))`.  The prize object
`M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖` therefore sits ABOVE `√d·(1 − o(1)) = √n·(1 − o(1))` in the
prize regime — the honest Plancherel `√n` floor on the correct off-DC object, in the sharp form. -/
theorem exists_offDC_peak_ge_sqrt_sharpFloor {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      Real.sqrt ((d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1)))
        ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := by
  obtain ⟨k₀, hk₀mem, hk₀⟩ := exists_offDC_peak_sq_ge_sharpFloor hd hN1
  refine ⟨k₀, hk₀mem, ?_⟩
  have hnn : (0 : ℝ) ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := norm_nonneg _
  rw [show ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
        = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) by
      rw [Real.sqrt_sq hnn]]
  exact Real.sqrt_le_sqrt hk₀

end ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp

open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp in
#print axioms exists_offDC_peak_sq_ge_sharpFloor
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp in
#print axioms exists_offDC_peak_ge_sqrt_sharpFloor
