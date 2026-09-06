/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Bridge B50 [target E7] — window-interior assembly `Johnson < δ* < capacity` (#444)

**Spec.** ASSEMBLY: `δ* ∈ (Johnson, capacity)` from
  {B48 monotone, B47 tail, hypothesis `m* < k`}.
Combine the landed E1 bricks into the window-interior conclusion, naming `m* < k` as the one
remaining hypothesis.

## Substrate consumed (all axiom-clean, already landed)

* **B01 / E1 — master gap identity** (`_BridgeB01.lean`,
  `deltaStar_master_gap_identity`): `δ* = 1 − ρ − (m*−1)/n` with `ρ = k/n`, `m* = s* − k`.
  We re-prove the exact ℝ-algebra inline here (it is the same `field_simp;ring` brick over ℝ) so
  this file's only imports are light analysis lemmas, and consume it as the closed form.
* **B02 / E1 — Johnson-crossing biconditional** (`_BridgeB02.lean`,
  `deltaStar_gt_johnson_iff_mstar_lt`): `1 − √ρ < δ* ↔ m* < (√ρ − ρ)·n + 1`. This is the genuine
  Johnson-side lower input — the **"B47 tail"** face (the cascade tail must bind shallow enough,
  `m* < (√ρ−ρ)n+1`, to cross Johnson).
* The capacity-side **"B48 monotone"** face: `δ* < capacity = 1 − ρ ↔ 1 < m*` (a binder strictly
  past depth 1 — the over-determination is genuinely ≥ 2, which the cascade E2 supplies:
  `m* = 3,3,5` for `n = 8,16,32`).

## The assembly

The window-interior conclusion `1 − √ρ < δ* < 1 − ρ` decomposes into the two crossings:

* **Capacity (upper):** `δ* < 1 − ρ  ⟺  1 < m*`.  Proved from E1 by `1 < m* ⟹ (m*−1)/n > 0`.
* **Johnson (lower):** `1 − √ρ < δ*  ⟺  m* < (√ρ − ρ)·n + 1` (B02).

The spec asks to name **`m* < k`** as the single remaining hypothesis. We show this is a *genuine
sufficient surrogate in the prize regime* `ρ ≤ 1/4` (the project rates `ρ ∈ {1/4,1/8,1/16}`):
in that regime `√(k n) ≥ 2k`, so

  `(√ρ − ρ)·n + 1 = √(k n) − k + 1 ≥ 2k − k + 1 = k + 1 > k`,

hence `m* < k ⟹ m* < (√ρ − ρ)·n + 1`, discharging the Johnson side via B02. Combined with the
capacity side `2 ≤ m*` (which `m* < k` makes nonvacuous, since it needs `k ≥ 3`), this lands the
full window-interior statement modulo the SINGLE explicit hypothesis `m* < k` (and the tail bound
`2 ≤ m*`, the E2-cascade fact that the binder is past depth 1).

## Honesty

This is an **honest reduction (REDUCED-style assembly)**: every step is forced ℝ-algebra from E1 +
B02-shaped inequalities. The genuine open content (that the *operational* `δ*` equals the closed
form, and that `m* < k` actually holds for explicit RS — i.e. the E7 `m* = O(log n)` growth law /
BCHKS 1.12) lives entirely in the named hypotheses `hE1` and `hmk : m* < k`; nothing here discharges
it. The axiom audit must show only a subset of `{propext, Classical.choice, Quot.sound}`.

Issue #444.
-/

namespace ArkLib.ProximityGap.BridgeB50

open Real

/-- **E1 (master gap identity, ℝ form).** From `ρ = k/n`, `m* = s − k`,
`δ* = 1 − (s−1)/n`, the gap identity `δ* = 1 − ρ − (m*−1)/n` is forced. (ℝ port of B01.) -/
theorem deltaStar_master_gap_identity
    (n k s deltaStar rho mstar : ℝ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - (s - 1) / n) :
    deltaStar = 1 - rho - (mstar - 1) / n := by
  subst hρ hms hδ; field_simp; ring

/-- **Capacity side ("B48 monotone").** Given E1, the threshold is strictly below capacity
`1 − ρ` iff the binding depth is strictly past `1`. -/
theorem deltaStar_lt_capacity_iff_one_lt_mstar
    (n rho mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n) :
    deltaStar < 1 - rho ↔ 1 < mstar := by
  rw [hE1]
  rw [show (1 - rho - (mstar - 1) / n < 1 - rho) ↔ (0 < (mstar - 1) / n) by
        constructor <;> intro h <;> linarith]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · exact absurd hn (not_lt.mpr (le_of_lt h))
  · intro h; exact Or.inl ⟨by linarith, hn⟩

/-- **Johnson side ("B47 tail").** Given E1, the threshold is strictly above Johnson `1 − √ρ`
iff `m* < (√ρ − ρ)·n + 1`. (ℝ port of B02 `deltaStar_gt_johnson_iff_mstar_lt`.) -/
theorem deltaStar_gt_johnson_iff_mstar_lt
    (rho n mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n) :
    (1 - Real.sqrt rho < deltaStar) ↔ (mstar < (Real.sqrt rho - rho) * n + 1) := by
  rw [hE1]
  rw [show (1 - Real.sqrt rho < 1 - rho - (mstar - 1) / n)
        ↔ ((mstar - 1) / n < (Real.sqrt rho - rho)) by
        constructor <;> intro h <;> linarith]
  rw [div_lt_iff₀ hn]
  constructor <;> intro h <;> nlinarith [h]

/-- **Prize-regime tail surrogate.** In the prize regime `ρ ≤ 1/4` (`ρ ∈ {1/4,1/8,1/16}`), the
Johnson-crossing threshold `(√ρ − ρ)·n + 1` is at least `k + 1` (where `k = ρ·n`), because
`√ρ ≥ 2ρ` there. Hence `m* < k` is a sufficient surrogate for `m* < (√ρ − ρ)·n + 1`. -/
theorem mstar_lt_johnson_threshold_of_lt_k
    (rho n k mstar : ℝ) (hn : 0 < n)
    (hk : k = rho * n) (hρpos : 0 < rho) (hρ4 : rho ≤ 1 / 4)
    (hmk : mstar < k) :
    mstar < (Real.sqrt rho - rho) * n + 1 := by
  -- `√ρ ≥ 2ρ` on `0 < ρ ≤ 1/4`: square both sides (`(2ρ)² = 4ρ² ≤ ρ = (√ρ)²` since `4ρ ≤ 1`).
  have hsqrt : 2 * rho ≤ Real.sqrt rho := by
    have h4 : (2 * rho) ^ 2 ≤ rho := by nlinarith [hρpos, hρ4]
    have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt hρpos)
    nlinarith [Real.sqrt_nonneg rho, hsq, h4, hρpos]
  -- Then `(√ρ − ρ)·n ≥ (2ρ − ρ)·n = ρ·n = k`, so the threshold `≥ k + 1 > k > m*`.
  have hkle : k ≤ (Real.sqrt rho - rho) * n := by
    have : rho * n ≤ (Real.sqrt rho - rho) * n := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hn); linarith
    rw [hk]; linarith
  linarith

/-- **B50 — window-interior assembly.**

Inputs (all named, nothing discharged):
* `hE1` — E1 master gap identity (B01 face): `δ* = 1 − ρ − (m*−1)/n`.
* `hk`  — rate normalization `k = ρ·n`.
* `0 < ρ ≤ 1/4` — the prize regime (`ρ ∈ {1/4,1/8,1/16}`).
* `htail : 2 ≤ m*` — the **B47 tail** fact (E2 cascade: the binder is past depth 1; `m* ≥ 2`,
  in fact `m* = 3,3,5` for `n = 8,16,32`).
* `hmk : m* < k` — **the ONE remaining hypothesis** (the E7 `m*` growth law / BCHKS 1.12).

Conclusion: the threshold is window-interior, `1 − √ρ < δ* < 1 − ρ`. -/
theorem deltaStar_window_interior
    (n k rho mstar deltaStar : ℝ) (hn : 0 < n)
    (hE1 : deltaStar = 1 - rho - (mstar - 1) / n)
    (hk : k = rho * n) (hρpos : 0 < rho) (hρ4 : rho ≤ 1 / 4)
    (htail : 2 ≤ mstar)
    (hmk : mstar < k) :
    1 - Real.sqrt rho < deltaStar ∧ deltaStar < 1 - rho := by
  refine ⟨?_, ?_⟩
  · -- Johnson side via the B02 biconditional + the prize-regime tail surrogate.
    rw [deltaStar_gt_johnson_iff_mstar_lt rho n mstar deltaStar hn hE1]
    exact mstar_lt_johnson_threshold_of_lt_k rho n k mstar hn hk hρpos hρ4 hmk
  · -- Capacity side via the B48 monotone biconditional + `m* ≥ 2 > 1`.
    rw [deltaStar_lt_capacity_iff_one_lt_mstar n rho mstar deltaStar hn hE1]
    linarith

end ArkLib.ProximityGap.BridgeB50

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound`) -/
#print axioms ArkLib.ProximityGap.BridgeB50.deltaStar_master_gap_identity
#print axioms ArkLib.ProximityGap.BridgeB50.deltaStar_lt_capacity_iff_one_lt_mstar
#print axioms ArkLib.ProximityGap.BridgeB50.deltaStar_gt_johnson_iff_mstar_lt
#print axioms ArkLib.ProximityGap.BridgeB50.mstar_lt_johnson_threshold_of_lt_k
#print axioms ArkLib.ProximityGap.BridgeB50.deltaStar_window_interior
