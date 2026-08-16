/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# The r=3 DC-Wick rung for the 2-power-subgroup Gauss periods: `κ_6 = 40 n` and `κ_6 ≤ 45 n²` (#444)

This is the **r = 3 rung** of the DC-subtracted moment-Wick ladder consumed by
`Frontier/DCWickMGFFromTermwise.lean` (`DCWickBound G 3`, predicate `q·E_3 − n^6 ≤ q·15·n³`).
We attack its **cumulant face** `κ_6 ≤ 45 n²`.

## The exact char-0 inputs (probe `scripts/probes/probe_kappa6_dcwick_r3.py`, p ~ n^5, n = 16..256)

For the thin 2-power subgroup `μ_n` (`n = 2^μ`, `4 ∣ n`, so `η_b` real), the **char-0** additive
energies `E_r = #{(x₁..x_{2r}) ∈ μ_n^{2r} : Σ xᵢ = 0}` are EXACT integer polynomials in `n`:

* `E₁ = n`                       (PROVEN in tree: `REnergyTwoExact.rEnergy_one` / diagonal `r=1`).
* `E₂ = 3 n² − 3 n`              (PROVEN in tree: `REnergyTwoExact.mu_n_rEnergy_two_eq`, via the
                                  Sidon-mod-negation additive-energy pin, for `2^n < p`).
* `E₃ = 15 n³ − 45 n² + 40 n`    (**OPEN INPUT** — the depth-3 Lam–Leung antipodal-pair count;
                                  char-0 verified EXACT by the probe at `p ~ n^5` for `n = 16..256`,
                                  not yet Lean-formalized. This is the genuinely-open residual = the
                                  char-`p` Lam–Leung / BGK–Spur wall, here ONE named hypothesis `h3`.)

The DC-subtracted central moments are `μ_{2r} = E_r` (char-0 limit, since `S_{2r}/p = E_r − n^{2r}/p
→ E_r`), so the cumulants are the standard symmetric mean-0 combinations
* `κ₂ = μ₂ = E₁`
* `κ₄ = μ₄ − 3 μ₂² = E₂ − 3 E₁²`
* `κ₆ = μ₆ − 15 μ₄ μ₂ + 30 μ₂³ = E₃ − 15 E₂ E₁ + 30 E₁³`.

## What THIS file proves (all axiom-clean; the only OPEN input is the char-0 `E₃` value)

* `kappa4_eq` : with `E₁ = n`, `E₂ = 3n²−3n`,  `κ₄ = E₂ − 3E₁² = −3 n`  (pure algebra — the exact
  negative-kurtosis carrier; UNCONDITIONAL on the two PROVEN energy values).
* `kappa6_eq` : with additionally `E₃ = 15n³−45n²+40n`,  `κ₆ = E₃ − 15E₂E₁ + 30E₁³ = 40 n`
  (pure algebra; the `−45n²` and `15n³` of `E₃` cancel against `−15E₂E₁` and `30E₁³`, the `−3n`
  kurtosis donating the slack — leaving the bare linear `40 n`).
* `dcWick_r3_rung_budget` : `40 n ≤ 45 n²` for every real `n ≥ 1` (pure arithmetic).
* `kappa6_le_45nsq` : the **r=3 DCWickBound rung**, `κ₆ ≤ 45 n²`, assembled from the above.
  The slack `45n² − κ₆ = 45n² − 40n` is QUADRATIC-vs-LINEAR: the rung holds by a wide margin.

## Honest status (NOT a CORE closure)
`κ₄ = −3n` is UNCONDITIONAL on the two in-tree-proven energy values.  `κ₆ = 40n` and the rung
`κ₆ ≤ 45n²` are conditional on the **one open input** (the exact char-0 depth-3 energy
`E₃ = 15n³−45n²+40n`).  That input is the char-0 Lam–Leung count — the SAME wall as the rest of the
ladder, NOT a new obstruction.  This is ONE rung of the DC-Wick ladder; the prize floor needs the
full ladder `r ≤ log m`.  CORE of #444 stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.Kappa6R3

/-- **The 4th cumulant is exactly `−3 n`** (the negative-kurtosis carrier).  Given the two PROVEN
char-0 energies `E₁ = n` and `E₂ = 3n² − 3n`, the symmetric mean-0 4th cumulant
`κ₄ = E₂ − 3 E₁²` equals `−3 n`.  Unconditional pure algebra. -/
theorem kappa4_eq (n E1 E2 : ℝ) (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n) :
    E2 - 3 * E1 ^ 2 = -3 * n := by
  subst h1 h2; ring

/-- **The 6th cumulant is exactly `40 n`.**  Given all three char-0 energies — `E₁ = n`,
`E₂ = 3n²−3n` (both PROVEN in tree) and `E₃ = 15n³−45n²+40n` (the open depth-3 Lam–Leung count) —
the symmetric mean-0 6th cumulant `κ₆ = E₃ − 15 E₂ E₁ + 30 E₁³` equals `40 n`.  The cubic and
quadratic terms of `E₃` cancel exactly against `−15 E₂ E₁` and `30 E₁³`, leaving the bare linear
`40 n`.  Pure algebra. -/
theorem kappa6_eq (n E1 E2 E3 : ℝ)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n) (h3 : E3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) :
    E3 - 15 * E2 * E1 + 30 * E1 ^ 3 = 40 * n := by
  subst h1 h2 h3; ring

/-- **The r=3 budget inequality.**  `40 n ≤ 45 n²` for every real `n ≥ 1` (in fact `n ≥ 8/9`
suffices; for the dyadic `n = 2^μ ≥ 2` it is comfortable).  Pure arithmetic. -/
theorem dcWick_r3_rung_budget (n : ℝ) (hn : 1 ≤ n) : 40 * n ≤ 45 * n ^ 2 := by
  nlinarith [hn, sq_nonneg (n - 1)]

/-- **THE r=3 DCWickBound rung (cumulant face): `κ₆ ≤ 45 n²`.**  Assembled from `kappa6_eq`
(`κ₆ = 40n`, conditional on the three char-0 energies) and `dcWick_r3_rung_budget` (`40n ≤ 45n²`).
The slack `45n² − κ₆ = 45n² − 40n` is quadratic-vs-linear: the rung holds with a wide margin.
The `−3n` 4th cumulant (PROVEN) donates the `−45n²` of `E₃` that this rung needs. -/
theorem kappa6_le_45nsq (n E1 E2 E3 : ℝ) (hn : 1 ≤ n)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n) (h3 : E3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) :
    E3 - 15 * E2 * E1 + 30 * E1 ^ 3 ≤ 45 * n ^ 2 := by
  rw [kappa6_eq n E1 E2 E3 h1 h2 h3]
  exact dcWick_r3_rung_budget n hn

end ArkLib.ProximityGap.Frontier.Kappa6R3

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3.kappa4_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3.kappa6_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3.dcWick_r3_rung_budget
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3.kappa6_le_45nsq
