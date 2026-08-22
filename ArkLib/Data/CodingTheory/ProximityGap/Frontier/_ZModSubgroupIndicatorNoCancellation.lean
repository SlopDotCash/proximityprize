/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTLinftyFloor

/-!
# The subgroup indicator's DFT has NO `√`-cancellation: every value is `0` or `d` (#407 / #444)

A natural-but-WRONG attack on CORE would try to read the prize cancellation
`M(μ_n) ≤ C√(n·log(p/n))` off the *subgroup indicator* `1_{μ_d}` via the DFT-uncertainty substrate.
This file records, axiom-clean, why that object carries no cancellation at all: the DFT of the
order-`d` subgroup indicator is **two-valued** (exactly `d` on the dual subgroup, `0` elsewhere),
so its peak magnitude is the DC value `d`, NOT a `√d`-scale cancelled value.

> `subgroupIndicator_dft_norm_eq_zero_or_d` : `‖𝓕 1_{μ_d} k‖ = 0 ∨ ‖𝓕 1_{μ_d} k‖ = d`.
> `subgroupIndicator_dft_dc_eq_d`           : `‖𝓕 1_{μ_d} 0‖ = d` (the DC peak).
> `subgroupIndicator_dft_peak_eq_d`         : `∀ k, ‖𝓕 1_{μ_d} k‖ ≤ d`, with equality at `k = 0`;
>                                              so the peak is exactly `d`.

Consequence (`subgroupIndicator_floor_not_tight`): the general `L^∞`–`L^2` Plancherel floor
`max_k ‖𝓕Φ‖ ≥ √(‖Φ‖₂²)` (`_ZModDFTLinftyFloor`) is *far from tight* for the indicator — `‖Φ‖₂² = d`
gives the floor `√d`, but the actual peak is `d ≫ √d` (for `d ≥ 2`).  Hence the indicator exhibits
ZERO cancellation; the genuine CORE object is the **off-DC additive-character sum over `μ_n` at a
nonzero frequency**, a different function whose `√`-cancellation is the open prize, NOT readable
from the indicator's two-valued spectrum.  This is a guard-rail lemma foreclosing the "just use
the subgroup indicator" shortcut.  No CORE/cancellation/completion/anti-concentration/capacity
claim; it RULES OUT a naive route.  Axiom-clean.  Issue #407/#444.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.ZModSubgroupSaturation

namespace ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation

variable {N : ℕ} [NeZero N]

/-- The order-`d` indicator's DFT magnitude is **two-valued**: `‖𝓕 1_{μ_d} k‖` is either `0` or `d`.
There is no intermediate (`√`-cancelled) value. -/
theorem subgroupIndicator_dft_norm_eq_zero_or_d {d : ℕ} (hd : d ∣ N) (k : ZMod N) :
    ‖𝓕 (subgroupIndicator (N := N) d) k‖ = 0 ∨ ‖𝓕 (subgroupIndicator (N := N) d) k‖ = (d : ℝ) := by
  rw [dft_subgroupIndicator hd k]
  by_cases h : stdAddChar (-(((N / d : ℕ) : ZMod N)) * k) = 1
  · right; rw [if_pos h, Complex.norm_natCast]
  · left; rw [if_neg h, norm_zero]

/-- The **DC value** of the indicator's DFT is `d`: `‖𝓕 1_{μ_d} 0‖ = d`.  (At `k = 0` the character
argument is `0`, so the geometric sum is `∑_{j∈μ_d} 1 = d`.) -/
theorem subgroupIndicator_dft_dc_eq_d {d : ℕ} (hd : d ∣ N) :
    ‖𝓕 (subgroupIndicator (N := N) d) (0 : ZMod N)‖ = (d : ℝ) := by
  rw [dft_subgroupIndicator hd 0]
  have h0 : stdAddChar (-(((N / d : ℕ) : ZMod N)) * (0 : ZMod N)) = 1 := by
    simp [AddChar.map_zero_eq_one]
  rw [if_pos h0, Complex.norm_natCast]

/-- The indicator's DFT magnitude is bounded by `d` everywhere, and HITS `d` at the DC frequency
`k = 0`.  Hence the peak magnitude `max_k ‖𝓕 1_{μ_d} k‖` is exactly `d` (achieved at `k = 0`). -/
theorem subgroupIndicator_dft_peak_eq_d {d : ℕ} (hd : d ∣ N) :
    (∀ k : ZMod N, ‖𝓕 (subgroupIndicator (N := N) d) k‖ ≤ (d : ℝ))
      ∧ ‖𝓕 (subgroupIndicator (N := N) d) (0 : ZMod N)‖ = (d : ℝ) := by
  refine ⟨fun k => ?_, subgroupIndicator_dft_dc_eq_d hd⟩
  rcases subgroupIndicator_dft_norm_eq_zero_or_d hd k with h | h
  · rw [h]; positivity
  · rw [h]

/-- **Guard-rail: the indicator carries NO `√`-cancellation; the Plancherel floor is loose for it.**
The general `L^∞`–`L^2` floor (`_ZModDFTLinftyFloor.subgroupIndicator_dft_peak_ge_sqrt`) gives
`max_k ‖𝓕 1_{μ_d}‖ ≥ √d`, but the actual peak is the DC value `d`.  For `d ≥ 1`, `√d ≤ d`, and the
inequality is strict for `d ≥ 2` (`√d < d`): the indicator's spectrum is two-valued (`0` or `d`),
with no cancelled `√d`-scale value.  So the subgroup indicator is the WRONG object for CORE; the
genuine cancellation lives in the off-DC additive-character sum over `μ_n`, a different function.

We state the gap as: the `√d` floor is `≤` the true peak `d` (always), exhibiting that the floor
does not control the peak from above; there is slack `d − √d ≥ 0` the indicator does not cancel. -/
theorem subgroupIndicator_floor_not_tight {d : ℕ} (hd : d ∣ N) :
    Real.sqrt (d : ℝ) ≤ ‖𝓕 (subgroupIndicator (N := N) d) (0 : ZMod N)‖
      ∧ ‖𝓕 (subgroupIndicator (N := N) d) (0 : ZMod N)‖ = (d : ℝ)
      ∧ Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
  have hpeak : ‖𝓕 (subgroupIndicator (N := N) d) (0 : ZMod N)‖ = (d : ℝ) :=
    subgroupIndicator_dft_dc_eq_d hd
  refine ⟨?_, hpeak, ?_⟩
  · -- √d ≤ peak = d, and √d ≤ d for natural d (√d ≤ d when d ≥ 1; d = 0 gives 0 ≤ 0)
    rw [hpeak]
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpos
      calc Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) * (d : ℝ)) := by
            apply Real.sqrt_le_sqrt; nlinarith [h1]
        _ = (d : ℝ) := by rw [Real.sqrt_mul_self (by positivity)]
  · rcases Nat.eq_zero_or_pos d with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpos
      calc Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) * (d : ℝ)) := by
            apply Real.sqrt_le_sqrt; nlinarith [h1]
        _ = (d : ℝ) := by rw [Real.sqrt_mul_self (by positivity)]

end ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation.subgroupIndicator_dft_norm_eq_zero_or_d
#print axioms
  ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation.subgroupIndicator_dft_dc_eq_d
#print axioms
  ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation.subgroupIndicator_dft_peak_eq_d
#print axioms
  ProximityGap.Frontier.ZModSubgroupIndicatorNoCancellation.subgroupIndicator_floor_not_tight
