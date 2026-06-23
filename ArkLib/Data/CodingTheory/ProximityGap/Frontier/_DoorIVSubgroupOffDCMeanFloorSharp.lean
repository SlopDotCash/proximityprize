/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupParsevalEnergyExact

/-!
# The off-DC mean-energy floor is two-sided sharp: it converges to the subgroup order (#444 door-iv)

The companion `_DoorIVSubgroupParsevalEnergyExact.subgroupIndicator_offDC_mean_le_order` proves the
ONE-sided bound that the off-DC mean energy is `≤ d`:
```
        (N·d − d²)/(N − 1)  ≤  d.
```
What was MISSING: the matching LOWER bound, which pins the mean floor in a TIGHT two-sided band that
converges to the subgroup order `d` as `N → ∞`.  The exact off-DC mean is
```
        (N·d − d²)/(N − 1)  =  d·(N − d)/(N − 1),
```
and `(N − d)/(N − 1) = 1 − (d − 1)/(N − 1) ≥ 1 − (d − 1)/(N − 1)`, so
```
        d·(1 − (d − 1)/(N − 1))  ≤  (N·d − d²)/(N − 1)  ≤  d.
```
In the prize regime `N = q ≈ d^β` (`β ≈ 4-5`), the relative defect `(d − 1)/(N − 1) ≈ d^{1−β} → 0`,
so the off-DC mean floor is `d·(1 − o(1))` — i.e. the Plancherel floor `√(mean) = √n·(1 − o(1))`
is asymptotically EXACTLY the prize scale `√n`.  This two-sided sharpness certifies that the lower
endpoint of the Shaw bracket is tight: the prize bound, if it holds, must sit just above `√n` (the
honest floor), with the door-(iv) gap being the multiplicative `√(log(p/n))` factor and NOTHING in
the floor itself.

* `subgroupIndicator_offDC_mean_eq` : closed form `(N·d − d²)/(N − 1) = d·(N − d)/(N − 1)`.
* `subgroupIndicator_offDC_mean_ge` : the matching lower bound `d·(1 − (d − 1)/(N − 1)) ≤ mean`.
* `subgroupIndicator_offDC_mean_two_sided` : the tight band `d·(1 − (d−1)/(N−1)) ≤ mean ≤ d`.

NOTE on scope: this is the SHARPNESS of the Plancherel floor (lower endpoint of the Shaw bracket) —
it pins the floor in a relative band of width `(d − 1)/(N − 1) → 0`, certifying the floor is `√n` to
leading order.  It is NOT the open CORE upper bound (the off-DC PEAK, not the mean), which is the
prize wall.  No cancellation, completion, anti-concentration, moment, or capacity claim.  CORE
remains OPEN; door (iv) remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- **Exact closed form of the off-DC mean energy.**  `(N·d − d²)/(N − 1) = d·(N − d)/(N − 1)`.
This is the empirical mean of the off-DC spectral energy over the `N − 1` off-DC frequencies, in
the factored form that exposes the relative defect `(N − d)/(N − 1)`. -/
theorem subgroupIndicator_offDC_mean_eq {d : ℕ} (hN1 : 1 < N) :
    ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
      = (d : ℝ) * (((N : ℝ) - d) / ((N : ℝ) - 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    linarith
  rw [mul_div_assoc']
  congr 1
  ring

omit [NeZero N] in
/-- **Matching lower bound on the off-DC mean energy (two-sided sharpness).**  The off-DC mean
is at least `d·(1 − (d − 1)/(N − 1))`.  Together with the companion's `≤ d`, the mean is pinned in a
relative band of width `(d − 1)/(N − 1)`, which `→ 0` in the prize regime `N ≈ d^β`.  Proof: the
exact mean is `d·(N − d)/(N − 1)` and `(N − d)/(N − 1) = 1 − (d − 1)/(N − 1)`, so the bound is an
equality at this endpoint. -/
theorem subgroupIndicator_offDC_mean_ge {d : ℕ} (hN1 : 1 < N) :
    (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
      ≤ ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1) := by
  have hNpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    linarith
  rw [subgroupIndicator_offDC_mean_eq hN1]
  -- show d·(1 − (d−1)/(N−1)) ≤ d·((N − d)/(N − 1)); in fact they are EQUAL
  have hkey : (1 : ℝ) - ((d : ℝ) - 1) / ((N : ℝ) - 1)
      = ((N : ℝ) - d) / ((N : ℝ) - 1) := by
    field_simp
    ring
  rw [hkey]

/-- **Two-sided tight band on the off-DC mean energy.**  Combining the matching lower bound with the
companion's upper bound:
```
        d·(1 − (d − 1)/(N − 1))  ≤  (N·d − d²)/(N − 1)  ≤  d.
```
The relative defect `(d − 1)/(N − 1) → 0` in the prize regime `N ≈ d^β`, so the Plancherel floor
`√(off-DC mean) = √n·(1 − o(1))` is asymptotically EXACTLY the prize scale `√n`.  The lower endpoint
of the Shaw bracket is thus tight; the door-(iv) gap is the multiplicative `√(log(p/n))` factor
sitting ABOVE this sharp floor, not inside it. -/
theorem subgroupIndicator_offDC_mean_two_sided {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    (d : ℝ) * (1 - ((d : ℝ) - 1) / ((N : ℝ) - 1))
        ≤ ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
      ∧ ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1) ≤ (d : ℝ) := by
  refine ⟨subgroupIndicator_offDC_mean_ge hN1, ?_⟩
  -- the companion's `_le_order` is stated on the SUM/(N−1); rewrite the sum to its closed form
  have hle := subgroupIndicator_offDC_mean_le_order hd hN1
  rwa [subgroupIndicator_offDC_energy hd] at hle

end ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp

open ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp in
#print axioms subgroupIndicator_offDC_mean_eq
open ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp in
#print axioms subgroupIndicator_offDC_mean_ge
open ProximityGap.Frontier.DoorIVSubgroupOffDCMeanFloorSharp in
#print axioms subgroupIndicator_offDC_mean_two_sided
