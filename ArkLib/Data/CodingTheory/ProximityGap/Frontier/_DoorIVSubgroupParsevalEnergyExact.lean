/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTParseval
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModSubgroupSaturation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDonohoStark

/-!
# The exact thin-subgroup Plancherel energy and its DC-subtracted off-frequency form (#444 door-iv)

The door-(iv) moment-floor → tetrachotomy bridge (`_DoorIVMomentFloorTetrachotomyBridge`)
discharges its headline from a *hypothesis* `hPlancherel : E_1 / card = n` (the normalized first
energy moment of the period field equals the subgroup order).  That normalization is exactly the
**Parseval / Plancherel identity** for the thin-subgroup indicator, and the substrate already lands
the analytic input (`_ZModDFTParseval.dft_parseval` : `∑_k ‖𝓕Φ k‖² = N·∑_j ‖Φ j‖²`) together with
the subgroup-indicator DFT machinery (`_ZModSubgroupSaturation.subgroupIndicator`, its `ℓ²`-mass
`= d`, geometric-sum DFT).  What was MISSING: nobody specialized Parseval to the indicator to land
the EXACT spectral energy as an *equality* (only the one-sided `L∞`-`L²` floor of
`_ZModDFTLinftyFloor` existed), and nobody landed the DC-subtracted off-frequency form — the
master-reduction-chain identity `Σ_{b≠0}|η_b|² = p·n − n²` of #444 §2.

This file closes that gap, axiom-clean, for the order-`d` subgroup indicator `1_{μ_d}` (`d ∣ N`):

* `subgroupIndicator_total_energy` : `∑_k ‖𝓕 1_{μ_d} k‖² = N·d`  (Parseval ∘ `ℓ²`-mass `= d`).
* `dft_subgroupIndicator_zero`     : `𝓕 1_{μ_d} 0 = d`  (DC value, the geometric sum at `k = 0`).
* `subgroupIndicator_offDC_energy` : `∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d²`  (= the #444 §2 master
  identity `p·n − n²` with `p = N`, `n = d`).
* `subgroupIndicator_offDC_mean_le_order` : the mean of the off-DC energy over the `N−1` off-DC
  frequencies is `≤ d` — the exact `E_1/card ≈ n` normalization the moment-floor bridge ASSUMES,
  now PROVEN (as the floor inequality) from the actual Parseval substrate.

NOTE on scope: this is the EXACT Plancherel ENERGY (an equality) plus its elementary consequences
— the *floor*/normalization substrate, the lower endpoint of the Shaw bracket.  It is NOT the open
CORE upper bound `M(μ_n) ≤ C√(n·log(p/n))` over the off-DC frequencies, which controls the
per-frequency PEAK, not the average.  The mean energy being `≈ d` is precisely *why* the
per-frequency peak floor is `√d` and why a moment mechanism cannot descend below it; it makes NO
cancellation, completion, anti-concentration, moment-saving, or capacity claim.  CORE remains
OPEN.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact

open ProximityGap.Frontier.ZModSubgroupSaturation
open ProximityGap.Frontier.ZModDFTParseval
open ProximityGap.Frontier.ZModDonohoStark

variable {N : ℕ} [NeZero N]

/-- **Exact thin-subgroup Plancherel energy.**  For the order-`d` subgroup indicator (`d ∣ N`) the
full spectral energy equals `N·d`: Parseval turns the `ℓ²`-mass `∑_j ‖Φ j‖² = d` (the support is `d`
unit-value points) into `∑_k ‖𝓕Φ k‖² = N·d`.  This is the two-sided energy *equality*, not the
one-sided floor of `_ZModDFTLinftyFloor`. -/
theorem subgroupIndicator_total_energy {d : ℕ} (hd : d ∣ N) :
    (∑ k : ZMod N, ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2) = (N : ℝ) * d := by
  have hmass : (∑ j : ZMod N, ‖(subgroupIndicator (N := N) d) j‖ ^ 2) = (d : ℝ) := by
    rw [sum_sq_eq_supp]
    have hone : ∀ j ∈ supp (subgroupIndicator (N := N) d),
        ‖(subgroupIndicator (N := N) d) j‖ ^ 2 = 1 := by
      intro j hj
      simp only [supp, mem_filter, mem_univ, true_and] at hj
      simp only [subgroupIndicator] at hj ⊢
      by_cases hk : (d : ZMod N) * j = 0
      · simp [hk]
      · simp only [if_neg hk, ne_eq, not_true_eq_false] at hj
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one,
      supp_subgroupIndicator_card hd]
  rw [dft_parseval, hmass]

/-- **DC value of the subgroup-indicator DFT.**  At the zero frequency the geometric sum collapses
to the full mass: `𝓕 1_{μ_d} 0 = d`.  (At `k = 0` the character argument is `0`, so
`stdAddChar 0 = 1` and the `if`-branch in `dft_subgroupIndicator` takes the value `d`.) -/
theorem dft_subgroupIndicator_zero {d : ℕ} (hd : d ∣ N) :
    (𝓕 (subgroupIndicator (N := N) d)) 0 = (d : ℂ) := by
  rw [dft_subgroupIndicator hd]
  simp

/-- The DC squared magnitude is `d²`. -/
theorem dft_subgroupIndicator_zero_normSq {d : ℕ} (hd : d ∣ N) :
    ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ ^ 2 = (d : ℝ) ^ 2 := by
  rw [dft_subgroupIndicator_zero hd, Complex.norm_natCast]

/-- **The DC-subtracted Plancherel identity (master-reduction-chain `Σ_{b≠0}|η_b|² = p·n − n²`).**
Subtracting the DC term `‖𝓕Φ 0‖² = d²` from the exact total energy `N·d` leaves the off-DC energy
`∑_{k≠0} ‖𝓕 1_{μ_d} k‖² = N·d − d²` — the exact #444 §2 identity (`p·n − n²` with `p = N`, `n = d`),
landed for the concrete subgroup indicator. -/
theorem subgroupIndicator_offDC_energy {d : ℕ} (hd : d ∣ N) :
    (∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
      = (N : ℝ) * d - (d : ℝ) ^ 2 := by
  have htot := subgroupIndicator_total_energy hd
  have hsplit : (∑ k : ZMod N, ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
      = ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ ^ 2
        + ∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2 := by
    rw [← Finset.sum_erase_add univ _ (Finset.mem_univ (0 : ZMod N))]; ring
  rw [hsplit, dft_subgroupIndicator_zero_normSq hd] at htot
  linarith

/-- The off-DC energy is bounded above by the full energy `N·d` (subtract a nonneg `d²`). -/
theorem subgroupIndicator_offDC_energy_le {d : ℕ} (hd : d ∣ N) :
    (∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
      ≤ (N : ℝ) * d := by
  rw [subgroupIndicator_offDC_energy hd]
  have : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- **The off-DC mean energy is `≤ d` — the bridge's `E_1/card = n` normalization, proven as a
floor.**  There are exactly `N − 1` off-DC frequencies of total energy `N·d − d²`, so the mean is
`(N·d − d²)/(N−1) = d·(N − d)/(N − 1) ≤ d` (since `1 ≤ d`).  This is precisely the normalization the
moment-floor tetrachotomy bridge *assumes* (`E_1/card = n`); here it is PROVEN — as the inequality
`mean off-DC energy ≤ d` — from the actual Parseval substrate, discharging the floor direction of
`hPlancherel` for the concrete subgroup indicator. -/
theorem subgroupIndicator_offDC_mean_le_order {d : ℕ} (hd : d ∣ N) (hN1 : 1 < N) :
    (∑ k ∈ (univ.erase (0 : ZMod N)), ‖(𝓕 (subgroupIndicator (N := N) d)) k‖ ^ 2)
        / ((N : ℝ) - 1) ≤ (d : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    linarith
  rw [subgroupIndicator_offDC_energy hd, div_le_iff₀ hNpos]
  have hdpos : 1 ≤ (d : ℝ) := by
    have hdnat : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · obtain ⟨e, he⟩ := hd; rw [h, zero_mul] at he; exact absurd he (NeZero.ne N)
      · exact h
    exact_mod_cast hdnat
  nlinarith [hdpos]

end ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact in
#print axioms subgroupIndicator_total_energy
open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact in
#print axioms subgroupIndicator_offDC_energy
open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact in
#print axioms subgroupIndicator_offDC_mean_le_order
