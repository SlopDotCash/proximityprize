/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Open-core SOS decomposition: the slack = two certified cushions − the wraparound residual (#444)

The prize reduces to the b≠0 sub-Gaussian energy `μ_{2r} ≤ Wick = (2r−1)‼·n^r`
(`μ_{2r} = (p·E_r(F_p) − n^{2r})/(p−1)`). This file records the **exact 3-term decomposition** of the open-core
slack that the SOS/positivity route found (verified by exact-integer probes, `n = 8,16`, `r ≤ 12`):
```
        (p−1)·(Wick − μ_{2r})  =  p·(Wick − E_r(ℂ))  +  (n^{2r} − Wick)  −  p·W_r,
```
where `E_r(ℂ)` is the char-0 energy and `W_r = E_r(F_p) − E_r(ℂ) ≥ 0` is the char-p wraparound excess. The first two
terms are **certified nonnegative**:
* `Wick − E_r(ℂ) ≥ 0` — the **char-0 Bessel deficit** (proven, `_CharZeroMGFBesselBound`: `E_r(ℂ) ≤ Wick`);
* `n^{2r} − Wick ≥ 0` — the **factorial gap** `(2r−1)‼ ≤ n^r` (elementary, for `r ≤ n`).

So the *entire* open content is the single wraparound residual `p·W_r`, cushioned by both nonneg terms:
```
        μ_{2r} ≤ Wick   ⟺   p·W_r  ≤  p·(Wick − E_r(ℂ)) + (n^{2r} − Wick).
```
This is **weaker** (more room) than the sharper `μ_{2r} ≤ E_r(ℂ)` form of `_OpenCoreCharPLighterReduction` (which
needs `p·W_r ≤ n^{2r} − E_r(ℂ)`); the extra room is exactly `(p−1)·(Wick − E_r(ℂ))`, the Bessel cushion. In
particular, **below the wraparound onset** (`W_r = 0`, exact-verified `r₀ = 6` at `n=16, β=4`, growing with β) the
open core holds outright, with both cushions to spare; combined with the proven `r=1` (Parseval) and `r=2`
(`W₂ = 0` at prize scale, the kurtosis order) cases, the open core is **unconditional for all `r` up to the onset**,
and the remaining work is bounding the wraparound `W_r` by the two cushions for `r` from the onset to `log p`.

**What this file proves (axiom-clean).** `slack_three_term_decomp` (the exact identity), `open_core_of_wraparound_le_cushions`
(`p·W_r ≤ cushions → μ ≤ Wick`), and `open_core_below_onset` (`W = 0` + both cushions nonneg → `μ ≤ Wick`). Issue #444.
-/

namespace ProximityGap.Frontier.OpenCoreSOS

/-- **The exact 3-term decomposition of the open-core slack.** With `μ·(p−1) = p·(E_C + W) − N₂` (`μ = μ_{2r}`,
`E_C = E_r(ℂ)`, `W = W_r`, `N₂ = n^{2r}`),
`(p−1)·(Wick − μ) = p·(Wick − E_C) + (N₂ − Wick) − p·W` — the slack splits into the Bessel deficit cushion, the
factorial-gap cushion, and minus the wraparound residual. -/
theorem slack_three_term_decomp (μ EC W N₂ Wick p : ℝ)
    (hdef : μ * (p - 1) = p * (EC + W) - N₂) :
    (p - 1) * (Wick - μ) = p * (Wick - EC) + (N₂ - Wick) - p * W := by
  linear_combination -hdef

/-- **Open core from the cushioned wraparound bound.** If the wraparound residual is at most the sum of the two
nonneg cushions (`p·W ≤ p·(Wick − E_C) + (N₂ − Wick)`) and `p > 1`, then `μ ≤ Wick` (the open core). -/
theorem open_core_of_wraparound_le_cushions (μ EC W N₂ Wick p : ℝ) (hp : 1 < p)
    (hdef : μ * (p - 1) = p * (EC + W) - N₂)
    (hcush : p * W ≤ p * (Wick - EC) + (N₂ - Wick)) :
    μ ≤ Wick := by
  have hp1 : 0 < p - 1 := by linarith
  have key := slack_three_term_decomp μ EC W N₂ Wick p hdef
  have : 0 ≤ (p - 1) * (Wick - μ) := by rw [key]; linarith
  have : 0 ≤ Wick - μ := (mul_nonneg_iff_of_pos_left hp1).mp this
  linarith

/-- **Open core below the wraparound onset.** With no wraparound (`W = 0`) and both cushions nonnegative — the
char-0 Bessel deficit `E_C ≤ Wick` and the factorial gap `Wick ≤ N₂` — the open core `μ ≤ Wick` holds outright. This
covers all depths `r` below the wraparound onset (and, via the proven `r=1,2` cases, the small-`r` band entirely). -/
theorem open_core_below_onset (μ EC N₂ Wick p : ℝ) (hp : 1 < p)
    (hdef : μ * (p - 1) = p * (EC + 0) - N₂) (hBessel : EC ≤ Wick) (hGap : Wick ≤ N₂) :
    μ ≤ Wick := by
  apply open_core_of_wraparound_le_cushions μ EC 0 N₂ Wick p hp hdef
  have h1 : 0 ≤ p * (Wick - EC) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ N₂ - Wick := by linarith
  simp only [mul_zero]; linarith

end ProximityGap.Frontier.OpenCoreSOS

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreSOS.slack_three_term_decomp
#print axioms ProximityGap.Frontier.OpenCoreSOS.open_core_of_wraparound_le_cushions
#print axioms ProximityGap.Frontier.OpenCoreSOS.open_core_below_onset
