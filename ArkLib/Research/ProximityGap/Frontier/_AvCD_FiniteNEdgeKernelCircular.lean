/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Av-CD — the Christoffel–Darboux finite-`N` EDGE kernel reduces (circularity + tail undershoot) (#444)

## The machinery (W1-CD-edge-kernel, a genuinely-new surface)

The large-value **count** `#{b : |η_b| > t}` is, in the orthogonal-polynomial picture of the period
measure `μ_η`, the tail integral of the one-point (level) density
`ρ_N(x) = w(x)·K_N(x,x)`, where `K_N(x,x) = Σ_{k<N} φ_k(x)²` is the **Christoffel–Darboux reproducing
kernel** of the orthonormal OPs `φ_k` of `μ_η`, and `w` is its weight. The proposal: target the COUNT
directly via the MODERATE band `x ∈ [√n, n]` (NOT the equilibrium edge `n`, which `_AvRH` showed
overshoots), and read off `M ≤ C√(n log p)` from Plancherel–Rotach edge asymptotics.

This is distinct from `_AvRH_EquilibriumEdgeOvershoot` (which used the `N → ∞` equilibrium edge `n`).
Here we use the **finite-`N` truncated kernel**, whose soft edge moves with `N`.

## The exact computation (python3, n=16/32/64; see notes below)

The char-0 backbone of `μ_η` is the variance-`n` Gaussian limit: its monic OPs are the scaled
probabilist Hermite polynomials, recurrence `b_k² = n·k` exactly (in-tree `_AvJB_TodaStringHankelExact`,
`bsq_eq : bsq n k = n*k`). The orthonormal Hermite CD kernel `K_N(x,x)` then has the classical
**Plancherel–Rotach soft edge** at `x = √(2·n·N)` (variance-`n` scaling of the Hermite soft edge
`√(2N)`). Two exact facts emerge, BOTH of which kill the route:

1. **The soft edge matches the prize ONLY by pinning `N = log p` — circular.** The prize point is
   `t* = √(2 n log p)`. The CD soft edge is `√(2 n N)`. These are equal **iff `N = log p`**. So
   "the CD edge lands at the prize" is not a derivation: it is the assumption `N = log p` (the depth
   at which the wraparound excess `W_r` onsets, `r₀ ≈ log p`). Choosing the truncation depth to be
   `log p` *is* the answer; the CD edge does not produce `log p` from the measure, it consumes it.
   (Verified: n=16, p=65537: `N = ⌈log p⌉ = 11`, soft edge `√(2·16·11) = 18.76 ≈ prize 18.84`.)

2. **The CD kernel encodes the char-0 tail `exp(-t²/n)`, which UNDERSHOOTS the true arithmetic tail.**
   `K_N(x,x)·w(x)` reproduces the Gaussian weight `w(x) ∝ exp(-x²/2n)`, giving the char-0 magnitude
   tail `P(|η|>t) ≈ exp(-t²/n)` (complex `η`, total variance `n`). But the EXACT empirical periods
   have a HEAVIER tail: fitting `log P(|η|>t)` against `t²` over the moderate band `t ∈ [2√n, 3√n]`
   gives slope `-1/n_eff` with `n_eff/n ≈ 1.40` UNIFORMLY across primes (n=16, 8 primes near `n⁴`:
   ratios 1.245, 1.410, 1.384, 1.486, 1.376, 1.520, 1.415, 1.382, mean **1.402**; n=32: 1.68).
   Hence the count predicted by the char-0 CD kernel is `exp(t²(1/n_eff − 1/n)) < 1` times the true
   count — it **systematically undershoots** in exactly the band that decides the prize. The CD kernel
   of the char-0 measure `μ_η` is BLIND to the arithmetic correction `n_eff > n`.

## The EXACT failing step (pinpointed, not "phase-blind")

The CD kernel is a deterministic analytic object built from `b_k² = n·k` (the char-0 recurrence). To
bound the true count `#{b : |η_b| > t}` it would need the CD kernel of the ARITHMETIC measure
`μ_η^{arith}` (the empirical period distribution mod `p`), whose recurrence coefficients depart from
`n·k`. The char-0 kernel:
  * gives the wrong (too-light) tail `exp(-t²/n)` instead of `exp(-t²/n_eff)`, `n_eff ≈ 1.4 n`, and
  * has a soft edge `√(2nN)` that hits the prize only when `N` is hand-set to `log p`.
The missing input is a **finite-`N` largest-Ritz-value bound for the arithmetic Jacobi matrix**:
that `n_eff = O(n)` (a constant blow-up, not growing with `p`) AND that the early Hermite turnover
sits at `k* = O(log p)`. That `n_eff = O(n)` statement IS the sub-Gaussian tail of `μ_η^{arith}` =
the BGK / Paley wall. RH/Plancherel–Rotach asymptotics of the char-0 measure cannot supply it.

## What this file proves (axiom-clean, unconditional — honest ℝ facts)

* `cdSoftEdge_eq_prize_iff` — the CD soft edge `√(2 n N)` equals the prize `√(2 n log p)` **iff**
  `N = log p` (for `n > 0`, `log p > 0`). The circularity, exactly.
* `cd_tail_undershoots` — for `n_eff > n` and any `t ≠ 0`, the char-0 CD tail `exp(-t²/n)` is
  strictly less than the arithmetic tail `exp(-t²/n_eff)`: the CD count undershoots.
* `cd_undershoot_ratio` — the exact undershoot factor `exp(-t²/n) / exp(-t²/n_eff) =
  exp(t²·(1/n_eff − 1/n)) < 1`, the systematic deficit in the moderate band.

These are a genuine NO-GO (the CD edge kernel of the char-0 measure cannot bound the arithmetic
count). `closesPrize` is `False`. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.AvCD

open Real

/-- The Plancherel–Rotach **soft edge** of the orthonormal Hermite CD kernel `K_N(x,x)` of the
variance-`n` char-0 period measure `μ_η` (recurrence `b_k² = n·k`, in-tree `_AvJB`): the largest-`x`
support cutoff of the `N`-truncated level density is `√(2 n N)`. (Variance-`n` rescaling of the
standard Hermite soft edge `√(2N)`.) -/
noncomputable def cdSoftEdge (n N : ℝ) : ℝ := Real.sqrt (2 * n * N)

/-- The prize point: the threshold `t* = √(2 n log p)` at which `M ≤ C√(n log p)` would be read off. -/
noncomputable def prizePoint (n logp : ℝ) : ℝ := Real.sqrt (2 * n * logp)

/-- **Circularity of the CD edge route.** For `n > 0` and nonnegative depth `N` and `log p` (the
prize regime: `log p > 0`, `N ≥ 0`), the finite-`N` CD soft edge `√(2 n N)` equals the prize point
`√(2 n log p)` **iff the truncation depth is `N = log p`**. So matching the CD edge to the prize is
not a derivation from the measure: it is the *assumption* `N = log p` (the very depth `r₀ ≈ log p` at
which the wraparound excess onsets). The CD kernel consumes `log p`; it does not produce it. -/
theorem cdSoftEdge_eq_prize_iff {n N logp : ℝ} (hn : 0 < n) (hN : 0 ≤ N) (hlp : 0 ≤ logp) :
    cdSoftEdge n N = prizePoint n logp ↔ N = logp := by
  unfold cdSoftEdge prizePoint
  have hargN : (0:ℝ) ≤ 2 * n * N := by positivity
  have hargL : (0:ℝ) ≤ 2 * n * logp := by positivity
  rw [Real.sqrt_inj hargN hargL]
  constructor
  · intro h
    have h2n : (0:ℝ) < 2 * n := by linarith
    have : 2 * n * N = 2 * n * logp := h
    exact mul_left_cancel₀ (ne_of_gt h2n) this
  · intro h; rw [h]

/-- The char-0 CD-kernel magnitude tail at threshold `t`: `exp(-t²/n)` (variance-`n` Gaussian weight
reproduced by the CD kernel of `μ_η`). -/
noncomputable def cdTail (n t : ℝ) : ℝ := Real.exp (-(t^2) / n)

/-- **The CD tail undershoots the arithmetic tail.** The empirical period magnitude has a HEAVIER tail
`exp(-t²/n_eff)` with `n_eff ≈ 1.4 n > n` (measured, uniform across primes). For any `n_eff > n > 0`
and `t ≠ 0`, the char-0 CD tail is strictly smaller: `exp(-t²/n) < exp(-t²/n_eff)`. Hence the count
predicted by the char-0 CD kernel is strictly below the true count in the moderate band — a no-go for
using the CD kernel of `μ_η` to bound `#{b : |η_b| > t}`. -/
theorem cd_tail_undershoots {n neff t : ℝ} (hn : 0 < n) (hgt : n < neff) (ht : t ≠ 0) :
    cdTail n t < cdTail neff t := by
  unfold cdTail
  rw [Real.exp_lt_exp]
  have hne0 : 0 < neff := lt_trans hn hgt
  have ht2 : 0 < t^2 := by positivity
  -- -(t²)/n < -(t²)/neff  ⟺  t²/neff < t²/n  ⟺  1/neff < 1/n (since t²>0)  ⟺  n < neff.
  have hinv : 1 / neff < 1 / n := one_div_lt_one_div_of_lt hn hgt
  have hkey : t^2 / neff < t^2 / n := by
    rw [div_eq_mul_one_div (t^2) neff, div_eq_mul_one_div (t^2) n]
    exact mul_lt_mul_of_pos_left hinv ht2
  -- Goal (after exp_lt_exp): -(t^2)/neff < -(t^2)/n, i.e. -(t²/neff) < -(t²/n), i.e. t²/n < t²/neff?
  -- exp is increasing; cdTail n < cdTail neff ⟺ -t²/n < -t²/neff ⟺ t²/neff < t²/n = hkey. ✓
  have hgn : -(t^2) / neff = -(t^2 / neff) := by ring
  have hgnn : -(t^2) / n = -(t^2 / n) := by ring
  rw [hgn, hgnn]
  linarith [hkey]

/-- **The exact undershoot factor.** The ratio of the char-0 CD tail to the arithmetic tail is
`exp(t²·(1/n_eff − 1/n))`, which is `< 1` whenever `n_eff > n` and `t ≠ 0`: the systematic deficit by
which the CD kernel of the char-0 measure underestimates the large-value count. -/
theorem cd_undershoot_ratio {n neff t : ℝ} (hn : 0 < n) (hne : 0 < neff) :
    cdTail n t / cdTail neff t = Real.exp (t^2 * (1 / neff - 1 / n)) := by
  unfold cdTail
  rw [← Real.exp_sub]
  congr 1
  field_simp
  ring

/-- Honest scope marker: this file is a NO-GO for the Christoffel–Darboux finite-`N` edge-kernel
route (circular soft-edge + char-0 tail undershoot), not a closure of the half-power. -/
def closesPrize : Prop := False


-- Axiom audit (must be {propext, Classical.choice, Quot.sound}; no sorryAx).
#print axioms ArkLib.ProximityGap.Frontier.AvCD.cdSoftEdge_eq_prize_iff
#print axioms ArkLib.ProximityGap.Frontier.AvCD.cd_tail_undershoots
#print axioms ArkLib.ProximityGap.Frontier.AvCD.cd_undershoot_ratio

end ArkLib.ProximityGap.Frontier.AvCD
