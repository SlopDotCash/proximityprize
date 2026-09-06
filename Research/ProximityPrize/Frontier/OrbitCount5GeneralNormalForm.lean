/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR5Bound

/-!
# The GENERAL-`g` orbit-count normal form of the `r = 5` deep-band census (#444)

`DeepBandR5Bound` (O181) PROVED the `r = 5` deep-band `#bad`-scalar closed form
`deepBandBadCount5 g = (4 g⁴ + 3 g³ + 12 − 10 g²)/12` (`g = n/4`) and DEFINED the half-order
(`d = n/2`) orbit count `deepBandFullOrb g = (4 g³ + 3 g² − 10 g)/24`, with the B2 orbit normal
form `#bad₅ = 1 + (n/2)·full_orb = 1 + 2g·full_orb`.  But that normal form is only certified at the
**four anchor rungs** `n = 16, 32, 64, 128` (`rung_orbit_n16 … rung_orbit_n128`, each `by decide`).
No GENERAL-`g` theorem states `deepBandBadCount5 g = 1 + 2g·deepBandFullOrb g`.

This file supplies it for **every even `g`** (the prize tower `g = n/4 = 2^{k-2}` is always even,
`g ∈ {4, 8, 16, 32, …}`), promoting the four point checks to a single closed identity:

> **`deepBandBadCount5 (2h) = 1 + 2·(2h)·deepBandFullOrb (2h)`** for all `h`.

## Mechanism (pure-ℕ, NOT a moment / energy method)

Writing the numerators `badnum = 12·#bad₅` and `orbnum = 24·full_orb`, the EXACT integer-polynomial
identity (division-free, verified symbolically) is

  `badnum = 12 + g·orbnum`,  i.e.  `4 g⁴ + 3 g³ + 12 − 10 g² = 12 + g·(4 g³ + 3 g² − 10 g)`.

Hence `1 + 2g·(orbnum/24) = 1 + g·(orbnum/12) = (12 + g·orbnum)/12 = badnum/12 = #bad₅`, provided
the two ℕ-divisions are exact.  `12 ∣ badnum` for even `g` is the in-tree
`DeepBandR5.twelve_dvd_r5_num_even`; the companion `24 ∣ orbnum` for even `g` is proved here
(`twentyfour_dvd_orb5_num_even`, period-3 residue sweep).  The headline then follows from the
already-proven `DeepBandR5.deepBandBadCount5_descent` plus the orbit-numerator's exactness.

## Honest scope

This is a **pure-ℕ structural identity** extending the proven `r = 5` closed form
(`DeepBandR5Bound`, O181) and the proven orbit normal form from 4 anchors to all even `g`.  It is
the orbit-COUNT general law for the ONE rung `r = 5` (the half-order `d = n/2` resonance maximizer,
which is why the orbit size here is `n/2`, NOT the full `n` of the `r = 3, 4` order-2 rungs).

It does **NOT** close CORE `M(μ_n) ≤ C·√(n·log(p/n))`.  The `r = 5` rung is already known strictly
sub-budget (deg `4` in `g` vs budget deg `5`, one full degree of headroom — `DeepBandR5Bound`); the
prize binds the DEEP rung `r ≈ log n` (`= |Σ_r(μ_s)|` = BCHKS 1.12 = the BGK wall), untouched here.
Character-sum-free, char-agnostic.  No capacity / beyond-Johnson / sub-linear / growth-law claim.

Probe: `scripts/probes/probe_orbit_count5_general.py` (PASS: `#bad₅ = 1 + 2g·full_orb` on the prize
tower `g = 2^{k-2}` `k = 4..16` and all even `g ≤ 200`; division-free core `badnum = 12 + g·orbnum`;
`24 ∣ orbnum` for even `g`; never `n = q − 1`).
-/

namespace ArkLib.ProximityGap.OrbitCount5GeneralNormalForm

open ArkLib.ProximityGap

/-- **`24 ∣ orbit numerator` for even `g`.**  The companion to the in-tree
`DeepBandR5.twelve_dvd_r5_num_even`: for `g = 2h`, `24 ∣ (4 g³ + 3 g² + 0 − 10 g)`, so the
ℕ-division
defining `deepBandFullOrb` is exact on the prize domain.  (Nat-subtraction is honest: `10·(2h) ≤
4·(2h)³ + 3·(2h)² + 0`.) -/
theorem twentyfour_dvd_orb5_num_even (h : ℕ) :
    (24 : ℕ) ∣ (4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 - 10 * (2 * h)) := by
  -- Nat-subtraction is honest: `10·(2h) ≤ 4(2h)³ + 3(2h)² + 0`.
  have hle : 10 * (2 * h) ≤ 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp
    · nlinarith [h0, Nat.one_le_iff_ne_zero.mpr (by positivity : h ^ 3 ≠ 0)]
  -- The honest numerator vanishes in `ZMod 24` (a `decide` over the 24 residues of the cubic).
  have hZmod : ((4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 - 10 * (2 * h) : ℕ) : ZMod 24) = 0 := by
    have hcast : ((4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 - 10 * (2 * h) : ℕ) : ZMod 24)
        = 4 * (2 * (h : ZMod 24)) ^ 3 + 3 * (2 * (h : ZMod 24)) ^ 2
            - 10 * (2 * (h : ZMod 24)) := by
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast]
    have key : ∀ x : ZMod 24, 4 * (2 * x) ^ 3 + 3 * (2 * x) ^ 2 - 10 * (2 * x) = 0 := by decide
    exact key _
  exact (ZMod.natCast_eq_zero_iff _ 24).mp hZmod

/-- **Exactness of `deepBandFullOrb` at even `g`.**  `24 * deepBandFullOrb (2h) = 4 (2h)³ + 3 (2h)²
+ 0 − 10 (2h)` — the ℕ-division in the definition recovers its numerator. -/
theorem twentyfour_mul_fullOrb_even (h : ℕ) :
    24 * DeepBandR5.deepBandFullOrb (2 * h)
      = 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 - 10 * (2 * h) := by
  rw [DeepBandR5.deepBandFullOrb, Nat.mul_div_cancel' (twentyfour_dvd_orb5_num_even h)]

/-- **GENERAL-`g` orbit-count normal form (HEADLINE).**  For every even `g = 2h` the `r = 5`
deep-band `#bad`-scalar closed form equals its B2 orbit normal form
`#bad₅ = 1 + (n/2)·full_orb = 1 + 2g·full_orb` (orbit size `d = n/2 = 2g`):

  `deepBandBadCount5 (2h) = 1 + 2·(2h)·deepBandFullOrb (2h)`.

This promotes the four anchor checks `rung_orbit_n16 … rung_orbit_n128` (`by decide`) to all even
`g`; the prize tower `g = n/4 = 2^{k-2}` is even for every `n = 2^k`, `k ≥ 4`. -/
theorem deepBandBadCount5_eq_orbit_normalForm (h : ℕ) :
    DeepBandR5.deepBandBadCount5 (2 * h)
      = 1 + 2 * (2 * h) * DeepBandR5.deepBandFullOrb (2 * h) := by
  -- The proven exactness bridges: 12·#bad₅ and 24·full_orb both recover their numerators.
  have hbad := DeepBandR5.deepBandBadCount5_descent h
  -- hbad : 12 * #bad₅(2h) + 10 (2h)^2 = 4 (2h)^4 + 3 (2h)^3 + 12
  have horb := twentyfour_mul_fullOrb_even h
  -- horb : 24 * full_orb(2h) = 4 (2h)^3 + 3 (2h)^2 + 0 - 10 (2h)
  have horb_le : 10 * (2 * h) ≤ 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp
    · nlinarith [h0, Nat.one_le_iff_ne_zero.mpr (by positivity : h ^ 3 ≠ 0)]
  -- Clear the subtraction in the orbit bridge:
  have horb' : 24 * DeepBandR5.deepBandFullOrb (2 * h) + 10 * (2 * h)
      = 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by omega
  -- The EXACT division-free polynomial identity (g = 2h):
  --   4 g⁴ + 3 g³ + 12 = 12 + g·(4 g³ + 3 g²).
  have hpoly : 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12
      = 12 + (2 * h) * (4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0) := by ring
  -- Abstract `g` and the bilinear `g·full_orb` as atoms so the closing step is LINEAR
  -- (no nonlinear `nlinarith` search over the degree-4 polynomial atoms).
  set F := DeepBandR5.deepBandFullOrb (2 * h) with hF
  set B := DeepBandR5.deepBandBadCount5 (2 * h) with hB
  have key : 12 * B = 12 + 24 * ((2 * h) * F) := by
    have hchain : 12 * B + 10 * (2 * h) ^ 2
        = 12 + 24 * ((2 * h) * F) + 10 * (2 * h) ^ 2 := by
      calc 12 * B + 10 * (2 * h) ^ 2
          = 4 * (2 * h) ^ 4 + 3 * (2 * h) ^ 3 + 12 := hbad
        _ = 12 + (2 * h) * (4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0) := hpoly
        _ = 12 + ((2 * h) * (24 * F) + (2 * h) * (10 * (2 * h))) := by rw [← horb']; ring
        _ = 12 + 24 * ((2 * h) * F) + 10 * (2 * h) ^ 2 := by ring
    omega
  -- goal: B = 1 + 2·(2h)·F = 1 + 2·((2h)·F); linear in `B` and the atom `(2h)·F`.
  have hgoal : 2 * (2 * h) * F = 2 * ((2 * h) * F) := by ring
  rw [hgoal]; omega

/-- **Spelled in `g` even.**  For even `g` (the prize tower `g = n/4 = 2^{k-2}`),
`deepBandBadCount5 g = 1 + 2g·deepBandFullOrb g`. -/
theorem deepBandBadCount5_eq_orbit_normalForm_even {g : ℕ} (hg : 2 ∣ g) :
    DeepBandR5.deepBandBadCount5 g = 1 + 2 * g * DeepBandR5.deepBandFullOrb g := by
  obtain ⟨h, rfl⟩ := hg
  simpa [two_mul, Nat.mul_comm] using deepBandBadCount5_eq_orbit_normalForm h

/-- **`r = 5` orbit count is STRICTLY SUPER-LINEAR (the half-order ThreadD obstruction).**  For the
prize tower `g = 2h ≥ 4` (`h ≥ 2`), the `r = 5` orbit count `full_orb(g)` exceeds `g`:
`2h < deepBandFullOrb (2h)`.  This is the `r = 5` half-order (`d = n/2`) analogue of O196's order-2
super-linearity (`orbitCount3 g > g`, `orbitCount4 (2h) > 2h`): the orbit count grows cubically
(`full_orb(2h) = h(h+1)(8h−5)/6`) while the ThreadD union-count floor needs orbit collapse `O ≤ 1`.
So the `O → 1` collapse CANNOT happen at the `r = 5` rung either; it can only occur at the deep
binding rung `r ≈ log n` (= the BGK/BCHKS wall). -/
theorem deepBandFullOrb_superlinear (h : ℕ) (hh : 2 ≤ h) :
    2 * h < DeepBandR5.deepBandFullOrb (2 * h) := by
  have hb := twentyfour_mul_fullOrb_even h
  have hle : 10 * (2 * h) ≤ 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by
    nlinarith [hh, Nat.one_le_iff_ne_zero.mpr (by positivity : h ^ 3 ≠ 0)]
  have hadd : 24 * DeepBandR5.deepBandFullOrb (2 * h) + 10 * (2 * h)
      = 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by omega
  nlinarith [hadd, hh, sq_nonneg h]

/-- Anchor sanity (matches the in-tree `rung_orbit_n16 … n128`): the general law reproduces the
four kernel-calibrated rungs. -/
theorem anchors_match :
    DeepBandR5.deepBandBadCount5 4 = 1 + 2 * 4 * DeepBandR5.deepBandFullOrb 4 ∧
    DeepBandR5.deepBandBadCount5 8 = 1 + 2 * 8 * DeepBandR5.deepBandFullOrb 8 ∧
    DeepBandR5.deepBandBadCount5 16 = 1 + 2 * 16 * DeepBandR5.deepBandFullOrb 16 ∧
    DeepBandR5.deepBandBadCount5 32 = 1 + 2 * 32 * DeepBandR5.deepBandFullOrb 32 :=
  ⟨by decide, by decide, by decide, by decide⟩

end ArkLib.ProximityGap.OrbitCount5GeneralNormalForm
