/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSubgroupOffDCPeakBracket

/-!
# The DC / off-DC spectral gap for the thin-subgroup indicator (#444 door-iv)

The off-DC substrate (`_DoorIVSubgroupOffDCPeakBracket`) pins the prize object
`M(μ_n) = max_{k≠0} ‖𝓕 1_{μ_d} k‖` below the trivial ℓ²-completion ceiling `√(N·d − d²)`.  The DC
coefficient is, by direct evaluation of the subgroup-indicator DFT,
```
        𝓕 1_{μ_d} 0 = d,         hence  ‖𝓕 1_{μ_d} 0‖ = d.
```
What was MISSING on the concrete object: the explicit DC / off-DC SPECTRAL GAP — the statement that
the off-DC peak is a `√(N/d)`-factor SMALLER than the DC coefficient.  This is the honest reason the
prize is about the *off-DC* maximum and not the (trivially huge) all-frequency maximum: the DC term
dominates by a square-root-of-thickness factor.

Combining `M² ≤ N·d − d²` (the off-DC ceiling) with `‖𝓕 1_{μ_d} 0‖² = d²`:
```
        M²  ≤  N·d − d²  =  ((N − d)/d) · d²  =  ((N − d)/d) · ‖𝓕 1_{μ_d} 0‖²,
```
i.e. `M ≤ √((N − d)/d) · ‖𝓕 1_{μ_d} 0‖ = √(N/d − 1) · ‖DC‖`.  In the prize regime `N = q ≈ d^β`
the gap factor is `√(N/d − 1) ≈ √(q/n) = n^{(β−1)/2}`: the off-DC peak is polynomially below the DC
coefficient, which is exactly why CORE localizes on the off-DC frequencies.

* `subgroupIndicator_dc_value`   : `𝓕 1_{μ_d} 0 = d`.
* `subgroupIndicator_dc_norm`    : `‖𝓕 1_{μ_d} 0‖ = d`.
* `offDC_peak_sq_le_gap_mul_dc_sq` : `M² ≤ ((N − d)/d) · ‖𝓕 1_{μ_d} 0‖²` (the DC/off-DC gap).

NOTE on scope: this is a structural SEPARATION between the DC coefficient and the off-DC peak — an
upper bound on the off-DC peak in terms of the DC coefficient, NOT the open CORE bound (which asks
for `M ≤ C·√(n·log(p/n))`, a `√(N/d)`-times STRONGER ceiling than the `√((N−d)/d)·d` recorded here).
The gap factor `√((N − d)/d)` is the trivial completion gap, recorded as the upper fence — NOT a
CORE bound.  No cancellation, anti-concentration, moment-saving, or capacity claim.  CORE remains
OPEN; door (iv) remains the only live door.  Axiom-clean.  Issue #444.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap

open ProximityGap.Frontier.DoorIVSubgroupParsevalEnergyExact
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakFloor
open ProximityGap.Frontier.DoorIVSubgroupOffDCPeakBracket
open ProximityGap.Frontier.ZModSubgroupSaturation

variable {N : ℕ} [NeZero N]

/-- **The DC coefficient of the subgroup indicator is the subgroup order.**  Evaluating the
subgroup-indicator DFT at the zero frequency: `𝓕 1_{μ_d} 0 = d`.  (At `k = 0` the geometric
character argument is `stdAddChar 0 = 1`, selecting the `(d : ℂ)` branch.) -/
theorem subgroupIndicator_dc_value {d : ℕ} (hd : d ∣ N) :
    (𝓕 (subgroupIndicator (N := N) d)) 0 = (d : ℂ) := by
  rw [dft_subgroupIndicator hd 0]
  have h0 : (-(((N / d : ℕ) : ZMod N)) * (0 : ZMod N)) = 0 := by ring
  rw [h0, AddChar.map_zero_eq_one, if_pos rfl]

/-- **The DC magnitude is the subgroup order.**  `‖𝓕 1_{μ_d} 0‖ = d`. -/
theorem subgroupIndicator_dc_norm {d : ℕ} (hd : d ∣ N) :
    ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ = (d : ℝ) := by
  rw [subgroupIndicator_dc_value hd, Complex.norm_natCast]

/-- **The DC / off-DC spectral gap.**  For any off-DC frequency `k₀ ≠ 0`, the squared magnitude is
at most `((N − d)/d)` times the squared DC magnitude:
```
        ‖𝓕 1_{μ_d} k₀‖²  ≤  ((N − d)/d) · ‖𝓕 1_{μ_d} 0‖².
```
Hence `M(μ_n) ≤ √(N/d − 1) · ‖DC‖`: the off-DC peak is a `√(N/d)`-factor below the DC coefficient.
This is the trivial completion gap (`√((N−d)/d)`), recorded as the upper fence, NOT a CORE bound. -/
theorem offDC_peak_sq_le_gap_mul_dc_sq {d : ℕ} (hd : d ∣ N)
    {k₀ : ZMod N} (hk₀ : k₀ ∈ (univ.erase (0 : ZMod N))) (hd0 : 0 < d) :
    ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2
      ≤ (((N : ℝ) - d) / d) * ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ ^ 2 := by
  have hceil := offDC_peak_sq_le_offDC_energy hd hk₀
  rw [subgroupIndicator_dc_norm hd]
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  -- ((N − d)/d)·d² = (N − d)·d = N·d − d²
  have hrhs : (((N : ℝ) - d) / d) * (d : ℝ) ^ 2 = (N : ℝ) * d - (d : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, mul_div_assoc, sq, mul_div_assoc, div_self hdpos.ne',
      mul_one]
    ring
  rw [hrhs]
  exact hceil


/-- **The DC / off-DC spectral gap (norm form).**  Taking square roots in
`offDC_peak_sq_le_gap_mul_dc_sq`, every off-DC coefficient is at most
`√((N-d)/d)` times the DC magnitude.  This is still the trivial completion gap,
not a CORE bound. -/
theorem offDC_peak_le_sqrt_gap_mul_dc {d : ℕ} (hd : d ∣ N)
    {k₀ : ZMod N} (hk₀ : k₀ ∈ (univ.erase (0 : ZMod N))) (hd0 : 0 < d) :
    ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
      ≤ Real.sqrt (((N : ℝ) - d) / d)
        * ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ := by
  have hsq := offDC_peak_sq_le_gap_mul_dc_sq hd hk₀ hd0
  have hk_nonneg : 0 ≤ ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ := norm_nonneg _
  have hNpos : 0 < N := NeZero.pos N
  have hdleN_nat : d ≤ N := Nat.le_of_dvd hNpos hd
  have hgap_nonneg : 0 ≤ (((N : ℝ) - d) / d) := by
    have hdleN : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdleN_nat
    have hdpos : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0.le
    exact div_nonneg (sub_nonneg.mpr hdleN) hdpos
  calc
    ‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖
        = Real.sqrt (‖(𝓕 (subgroupIndicator (N := N) d)) k₀‖ ^ 2) := by
          rw [Real.sqrt_sq hk_nonneg]
    _ ≤ Real.sqrt ((((N : ℝ) - d) / d)
          * ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((N : ℝ) - d) / d)
          * ‖(𝓕 (subgroupIndicator (N := N) d)) 0‖ := by
          rw [Real.sqrt_mul hgap_nonneg]
          rw [Real.sqrt_sq (norm_nonneg _)]

end ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap

open ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap in
#print axioms subgroupIndicator_dc_value
open ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap in
#print axioms subgroupIndicator_dc_norm
open ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap in
#print axioms offDC_peak_sq_le_gap_mul_dc_sq
open ProximityGap.Frontier.DoorIVSubgroupDCOffDCGap in
#print axioms offDC_peak_le_sqrt_gap_mul_dc
