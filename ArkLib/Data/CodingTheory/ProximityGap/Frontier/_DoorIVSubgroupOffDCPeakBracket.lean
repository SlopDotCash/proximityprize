/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakFloor

/-!
# The exact two-sided off-DC peak bracket for the thin-subgroup indicator (#444 door-iv)

The companion files land, for the order-`d` subgroup indicator `1_{μ_d}` (`d ∣ N`):

* `_DoorIVSubgroupParsevalEnergyExact.subgroupIndicator_offDC_energy` — the EXACT off-DC energy
  *equality* `∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d²` (the #444 §2 master identity `p·n − n²`);
* `_DoorIVSubgroupOffDCPeakFloor.exists_offDC_peak_sq_ge_mean` — the off-DC peak *floor*
  `M² ≥ (N·d − d²)/(N − 1)`.

What was still MISSING: the matching trivial **off-DC peak ceiling** and the resulting two-sided
*bracket* on the actual prize object `M(μ_n)² = max_{k≠0} ‖𝓕 1_{μ_d} k‖²`.  The ceiling is the
elementary half — a single nonneg term is at most the whole nonneg sum:
```
        max_{k≠0} ‖𝓕 1_{μ_d} k‖² ≤ ∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d².
```
Combined with the floor, this pins the off-DC peak EXACTLY inside the closed band
```
        (N·d − d²)/(N − 1)  ≤  M²  ≤  N·d − d²,
```
i.e. `√((N·d − d²)/(N − 1)) ≤ M ≤ √(N·d − d²)`.  In the prize regime `N = q ≈ d^β` (`β ≈ 4-5`) the
band is `[√d·(1 + o(1)), √(N·d)] = [√n·(1+o(1)), √(p·n)]` — exactly the **Plancherel floor `√n`** to
the **trivial ℓ²-completion ceiling `√(p·n)`**.  CORE asks for `M ≤ C·√(n·log(p/n))`, which is the
prize-width *inside* this band, far below the trivial completion ceiling — the band's width IS the
door-(iv) gap and CORE lives at its bottom.

* `offDC_peak_sq_le_offDC_energy` : the trivial ceiling `M² ≤ N·d − d²`.
* `exists_offDC_peak_sq_bracket`   : the EXACT two-sided band on `M²`.
* `exists_offDC_peak_bracket`      : the norm-form band on `M`.

NOTE on scope: BOTH endpoints are elementary (Plancherel floor + trivial ℓ²-completion ceiling).
The ceiling is the `√(p·n)`-completion bound the brief flags as *overshooting* (door (ii)); it is
recorded here ONLY to pin the band whose BOTTOM the prize must reach.  This is the floor/ceiling
substrate — NOT the open CORE upper bound, which would shrink the ceiling from `√(p·n)` to
`C·√(n·log(p/n))`.  No cancellation, anti-concentration, moment-saving, or capacity claim; door (ii)
completion is recorded as the *upper fence*, not as a CORE bound.  CORE remains OPEN; door (iv)
remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- **Trivial off-DC peak ceiling.**  Each off-DC squared magnitude is one nonnegative term of the
off-DC energy sum, so the off-DC peak (at any `k₀ ≠ 0`) is at most the whole off-DC energy
`N·d − d²`.  This is the elementary upper half of the bracket (the `√(p·n)` ℓ²-completion fence). -/
theorem offDC_peak_sq_le_offDC_energy {d : ℕ} (hd : d ∣ N)
    {k₀ : ZMod N} (hk₀ : k₀ ∈ (univ.erase (0 : ZMod N))) :
    ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 ≤ (N : ℝ) * d - (d : ℝ) ^ 2 := by
  rw [← subgroupIndicator_offDC_energy hd]
  refine Finset.single_le_sum (f := fun k => ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
    (fun k _ => sq_nonneg _) hk₀

/-- **Exact two-sided off-DC peak band (squared form).**  There is an off-DC argmax `k₀ ≠ 0` whose
squared magnitude is pinned between the off-DC mean energy and the off-DC total energy:
```
        (N·d − d²)/(N − 1)  ≤  ‖𝓕 1_{μ_d} k₀‖²  ≤  N·d − d².
```
The lower endpoint is the Plancherel floor (`exists_offDC_peak_sq_ge_mean`); the upper endpoint is
the trivial ℓ²-completion ceiling (`offDC_peak_sq_le_offDC_energy`). -/
theorem exists_offDC_peak_sq_bracket {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
          ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2
      ∧ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 ≤ (N : ℝ) * d - (d : ℝ) ^ 2 := by
  obtain ⟨k₀, hk₀mem, hfloor⟩ := exists_offDC_peak_sq_ge_mean hd hN1
  exact ⟨k₀, hk₀mem, hfloor, offDC_peak_sq_le_offDC_energy hd hk₀mem⟩

/-- **Exact two-sided off-DC peak band (norm form).**  The prize object
`M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖` is pinned between the Plancherel floor and the
ℓ²-completion ceiling:
```
        √((N·d − d²)/(N − 1))  ≤  ‖𝓕 1_{μ_d} k₀‖  ≤  √(N·d − d²).
```
In the prize regime this is `√n·(1+o(1)) ≤ M ≤ √(p·n)`: from the honest Plancherel floor to the
trivial completion ceiling.  CORE asks for `M ≤ C·√(n·log(p/n))`, strictly inside this band's
lower portion — the band width IS the door-(iv) gap. -/
theorem exists_offDC_peak_bracket {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      Real.sqrt (((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1))
          ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
      ∧ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
          ≤ Real.sqrt ((N : ℝ) * d - (d : ℝ) ^ 2) := by
  obtain ⟨k₀, hk₀mem, hfloor, hceil⟩ := exists_offDC_peak_sq_bracket hd hN1
  have hnn : (0 : ℝ) ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := norm_nonneg _
  refine ⟨k₀, hk₀mem, ?_, ?_⟩
  · -- floor (norm form)
    rw [show ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
          = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) by
        rw [Real.sqrt_sq hnn]]
    exact Real.sqrt_le_sqrt hfloor
  · -- ceiling (norm form)
    rw [show ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
          = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) by
        rw [Real.sqrt_sq hnn]]
    exact Real.sqrt_le_sqrt hceil

end ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket

open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket in
#print axioms offDC_peak_sq_le_offDC_energy
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket in
#print axioms exists_offDC_peak_sq_bracket
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket in
#print axioms exists_offDC_peak_bracket
