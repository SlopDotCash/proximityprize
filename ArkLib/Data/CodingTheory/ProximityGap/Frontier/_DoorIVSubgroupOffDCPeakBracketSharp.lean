/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakFloorSharp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakBracket

/-!
# The exact two-sided off-DC peak band in SHARP form (#444 door-iv)

`_DoorIVSubgroupOffDCPeakBracket` pins the prize object `M(μ_n)² = max_{k≠0} ‖𝓕 1_{μ_d} k‖²` in the
two-sided band `(N·d − d²)/(N − 1) ≤ M² ≤ N·d − d²`, whose lower endpoint is the *raw quotient*
form of the Plancherel floor.  `_DoorIVSubgroupOffDCPeakFloorSharp` then re-expressed that floor
against the *sharp closed form* `d·(1 − (d − 1)/(N − 1))`, making the `→ d` (i.e. `→ √n`)
convergence explicit.  What was MISSING: the two-sided BAND stated with the sharp floor as its
lower endpoint, so the whole bracket reads in the form whose `√n` lower limit is manifest.

This file composes the sharp floor
`_DoorIVSubgroupOffDCPeakFloorSharp.exists_offDC_peak_sq_ge_sharpFloor` with the existing trivial
ceiling `_DoorIVSubgroupOffDCPeakBracket.offDC_peak_sq_le_offDC_energy`:
```
        d·(1 − (d − 1)/(N − 1))  ≤  max_{k≠0} ‖𝓕 1_{μ_d} k‖²  ≤  N·d − d².
```
In the prize regime `N = q ≈ d^β` the band is `[d·(1 − o(1)), p·n − n²]` — from the SHARP Plancherel
floor `≈ √n` (now with explicit `o(1)` convergence) up to the trivial ℓ²-completion ceiling
`√(p·n)`.  CORE asks for `M ≤ C·√(n·log(p/n))`, strictly inside this band's lower portion; the band
width IS the door-(iv) gap.

* `exists_offDC_peak_sq_bracket_sharp` : ∃ argmax `k₀ ≠ 0` with
  `d·(1 − (d − 1)/(N − 1)) ≤ ‖𝓕 1_{μ_d} k₀‖² ≤ N·d − d²`.
* `exists_offDC_peak_bracket_sharp` : the norm form,
  `√(d·(1 − (d − 1)/(N − 1))) ≤ ‖𝓕 1_{μ_d} k₀‖ ≤ √(N·d − d²)`.

NOTE on scope: the lower endpoint is the SHARP Plancherel floor (lower bound — easy direction); the
upper endpoint is the trivial ℓ²-completion ceiling (door (ii), recorded ONLY as the upper fence
whose distance to the floor is the open gap, NOT as a CORE bound).  It proves NO CORE upper bound
and makes NO cancellation, anti-concentration, moment-saving, or capacity claim.  CORE remains OPEN;
door (iv) remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloorSharp
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- **Exact two-sided off-DC peak band in SHARP form (squared form).**  There is an off-DC argmax
`k₀ ≠ 0` whose squared magnitude is pinned between the SHARP Plancherel floor and the trivial
ℓ²-completion ceiling:
```
        d·(1 − (d − 1)/(N − 1))  ≤  ‖𝓕 1_{μ_d} k₀‖²  ≤  N·d − d².
```
Lower endpoint: `exists_offDC_peak_sq_ge_sharpFloor`.  Upper endpoint:
`offDC_peak_sq_le_offDC_energy`. -/
theorem exists_offDC_peak_sq_bracket_sharp {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
          ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2
      ∧ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 ≤ (N : ℝ) * d - (d : ℝ) ^ 2 := by
  obtain ⟨k₀, hk₀mem, hfloor⟩ := exists_offDC_peak_sq_ge_sharpFloor hd hN1
  exact ⟨k₀, hk₀mem, hfloor, offDC_peak_sq_le_offDC_energy hd hk₀mem⟩

/-- **Exact two-sided off-DC peak band in SHARP form (norm form).**  The prize object
`M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖` is pinned between the SHARP Plancherel floor and the
ℓ²-completion ceiling:
```
        √(d·(1 − (d − 1)/(N − 1)))  ≤  ‖𝓕 1_{μ_d} k₀‖  ≤  √(N·d − d²).
```
In the prize regime this is `√n·(1 − o(1)) ≤ M ≤ √(p·n)`: from the SHARP honest Plancherel floor
(with explicit `o(1)` convergence to `√n`) up to the trivial completion ceiling.  CORE asks for
`M ≤ C·√(n·log(p/n))`, strictly inside this band's lower portion — the band width IS the door-(iv)
gap. -/
theorem exists_offDC_peak_bracket_sharp {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      Real.sqrt ((d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1)))
          ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
      ∧ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
          ≤ Real.sqrt ((N : ℝ) * d - (d : ℝ) ^ 2) := by
  obtain ⟨k₀, hk₀mem, hfloor, hceil⟩ := exists_offDC_peak_sq_bracket_sharp hd hN1
  have hnn : (0 : ℝ) ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := norm_nonneg _
  have hrw : ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
        = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) := by
    rw [Real.sqrt_sq hnn]
  refine ⟨k₀, hk₀mem, ?_, ?_⟩
  · rw [hrw]; exact Real.sqrt_le_sqrt hfloor
  · rw [hrw]; exact Real.sqrt_le_sqrt hceil

end ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp

open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp in
#print axioms exists_offDC_peak_sq_bracket_sharp
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracketSharp in
#print axioms exists_offDC_peak_bracket_sharp
