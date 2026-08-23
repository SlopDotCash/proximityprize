/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupParsevalEnergyExact

/-!
# The exact off-DC peak floor for the thin-subgroup indicator (#444 door-iv)

The companion file `_DoorIVSubgroupParsevalEnergyExact` lands, for the order-`d` subgroup indicator
`1_{μ_d}` (`d ∣ N`), the EXACT off-DC spectral energy as an *equality*
```
        ∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d²            (the #444 §2 master identity `p·n − n²`)
```
and the off-DC *mean* energy floor `(N·d − d²)/(N − 1) ≤ d`.

What was still MISSING on the concrete subgroup-indicator object: the **off-DC PEAK floor**.  The
prize object `M(μ_n)` is the *off-DC* maximum `max_{k≠0} ‖𝓕 1_{μ_d} k‖`, NOT the all-frequency
maximum (which is the DC value `d ≫ √d` and tells you nothing about CORE).  The existing
`L∞`-`L²` floor (`_ZModDFTLinftyFloor.exists_dft_peak_sq_ge_l2`) maximizes over *all* frequencies
and is therefore dominated by the trivial DC term — it does NOT give a floor on the *off-DC* peak.

This file closes that gap with one averaging step, axiom-clean: the off-DC peak squared is at least
the off-DC MEAN energy, and the off-DC mean energy is EXACTLY `(N·d − d²)/(N − 1)` (the companion's
equality).  Hence
```
        max_{k≠0} ‖𝓕 1_{μ_d} k‖² ≥ (N·d − d²)/(N − 1) = d·(N − d)/(N − 1).
```
This is the CORRECT lower endpoint of the prize bracket for the actual prize object (the off-DC
peak), derived from the EXACT off-DC energy equality — no hypothesis, no DC contamination.

* `exists_offDC_peak_sq_ge_mean` : ∃ argmax `k₀ ≠ 0` with `(N·d − d²)/(N − 1) ≤ ‖𝓕 1_{μ_d} k₀‖²`.
* `exists_offDC_peak_ge_sqrt_mean` : the norm form, `√((N·d − d²)/(N − 1)) ≤ ‖𝓕 1_{μ_d} k₀‖`.

NOTE on scope: this is a FLOOR (lower bound) on the off-DC peak — the EASY direction, the lower
endpoint of the Shaw bracket, now landed for the off-DC object (not the DC-contaminated
all-frequency object).  In the prize regime `N = q ≈ d^β` the floor is `≈ √d = √n`
(since `(N·d − d²)/(N−1) → d`):
the honest Plancherel `√n` floor, on the *correct* off-DC object.  It does NOT touch CORE — the OPEN
upper bound `M(μ_n) ≤ C·√(n·log(p/n))` over the off-DC frequencies, which controls the off-DC peak
from ABOVE.  No cancellation, completion, anti-concentration, moment-saving, or capacity claim.
CORE remains OPEN; door (iv) remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- The off-DC frequency set `univ.erase 0` is nonempty when `1 < N` (`N − 1 ≥ 1` elements). -/
theorem offDC_nonempty (hN1 : 1 < N) :
    ((univ.erase (0 : ZMod N))).Nonempty := by
  have hcard : (univ.erase (0 : ZMod N)).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [← Finset.card_pos, hcard]
  omega

/-- The off-DC frequency set has real cardinality `N − 1`. -/
theorem offDC_card_eq :
    ((univ.erase (0 : ZMod N)).card : ℝ) = (N : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  rw [Nat.cast_sub hNpos, Nat.cast_one]

/-- **Off-DC peak squared ≥ off-DC mean energy (squared form).**  Over the `N − 1` off-DC
frequencies, the maximum squared magnitude `‖𝓕 1_{μ_d} k₀‖²` is at least the off-DC mean energy
`(N·d − d²)/(N − 1)`.  This is one averaging step off the companion's exact off-DC energy
equality `∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d²`. -/
theorem exists_offDC_peak_sq_ge_mean {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      ((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1)
        ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 := by
  have hne : ((univ.erase (0 : ZMod N))).Nonempty := offDC_nonempty hN1
  -- the off-DC argmax
  obtain ⟨k₀, hk₀mem, hk₀max⟩ :=
    Finset.exists_max_image (univ.erase (0 : ZMod N))
      (fun k => ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2) hne
  refine ⟨k₀, hk₀mem, ?_⟩
  -- mean ≤ N·(N−1)-many copies of the peak
  have hcardpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hsum_le :
      (∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
        ≤ ((N : ℝ) - 1) * ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 := by
    calc (∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
        ≤ ∑ _k ∈ (univ.erase (0 : ZMod N)),
            ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 :=
          Finset.sum_le_sum (fun k hk => hk₀max k hk)
      _ = ((N : ℝ) - 1) * ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, offDC_card_eq]
  rw [subgroupIndicator_offDC_energy hd] at hsum_le
  rw [div_le_iff₀ hcardpos]
  linarith [hsum_le]

/-- **Off-DC peak floor (norm form).**  There is an off-DC frequency `k₀ ≠ 0` whose DFT magnitude is
at least the square root of the exact off-DC mean energy:
`‖𝓕 1_{μ_d} k₀‖ ≥ √((N·d − d²)/(N − 1))`.  The prize object `M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖`
therefore sits ABOVE this honest Plancherel floor on the *correct off-DC object* (no DC
contamination).  In the prize regime `(N·d − d²)/(N−1) → d`, so this is the `√n` floor. -/
theorem exists_offDC_peak_ge_sqrt_mean {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    ∃ k₀ ∈ (univ.erase (0 : ZMod N)),
      Real.sqrt (((N : ℝ) * d - (d : ℝ) ^ 2) / ((N : ℝ) - 1))
        ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := by
  obtain ⟨k₀, hk₀mem, hk₀⟩ := exists_offDC_peak_sq_ge_mean hd hN1
  refine ⟨k₀, hk₀mem, ?_⟩
  have hnn : (0 : ℝ) ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := norm_nonneg _
  rw [show ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
        = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) by
      rw [Real.sqrt_sq hnn]]
  exact Real.sqrt_le_sqrt hk₀

end ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor

open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor in
#print axioms exists_offDC_peak_sq_ge_mean
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor in
#print axioms exists_offDC_peak_ge_sqrt_mean
