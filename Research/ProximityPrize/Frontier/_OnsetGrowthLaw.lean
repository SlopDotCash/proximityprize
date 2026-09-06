/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The wraparound onset law `r_0 = Θ(p^{1/φ(n)})` — and why it is BELOW the saddle at prize scale (#444)

A genuinely-new measurement + a framing CORRECTION (honest; not a closure).

## The measured law (probe `probe_onset_growth` / `onset_growth.py`, exact energy computation)

The **wraparound onset** `r_0(n,p)` = the smallest depth `r` at which `W_r = E_r(F_p) − E_r^{char0} ≠ 0` (the
first `r`-fold non-antipodal `±1`-relation of `n`-th roots that becomes divisible by `𝔭 | p` in `ℤ[ζ_n]`).
Exact computation (n=4 φ=2, n=8 φ=4, many p) gives the CLEAN law
```
r_0(n,p) = Θ( p^{1/φ(n)} ),   measured constant r_0 / p^{1/φ(n)} ∈ [0.77, 1.23]  (≈ 0.85–1.0).
```
So the onset is EXACTLY the Minkowski / shortest-`𝔭`-vector scale: a length-`2r` relation realizes an element of
`ℤ[ζ_n]` with every archimedean embedding `≤ 2r`, and the shortest nonzero `𝔭`-element (norm `p`) has that scale
at `r ~ p^{1/φ(n)}`. The 2-power cyclotomic structure gives NO improvement over the generic Minkowski bound.

## The CORRECTION (the framing this overturns)

Earlier framings (incl. memory `issue444-Wr-excess-onset-threshold`) read the small-`n` data as "`r_0 > r*`"
and hoped the prize is "no wraparound below the saddle `r* ≈ log p`". That holds for **fixed `n`, growing `p`**
(e.g. n=8, p≈n⁵: `r_0 ≈ p^{1/4} ≈ 13 > r* ≈ ln p ≈ 10`). But the prize is the **opposite limit — growing `n`**
with `p ≈ n^β`, and there the law INVERTS:
```
r_0 ≈ p^{1/φ(n)} = n^{β/φ(n)} = 2^{μβ/2^{μ−1}} → 1   as  μ → ∞,   while  r* ≈ ln p = μβ·ln 2 → ∞.
```
At the prize (`n = 2^30`, `φ(n) = 2^29`, `p ≈ 2^158`): `r_0 ≈ p^{1/2^29} = 2^{158/2^29} < 2`, far **below**
`r* ≈ 110`. **So at prize scale the wraparound is PERVASIVE (onset `≈ 1`), not absent.** The prize is therefore
the *quantitative* `W_r ≤ slack_r` at `r ≈ log p`, NOT the onset statement `r_0 > log p` (which is FALSE here).

Consequently the geometry-of-numbers route via the onset is vacuous: the lattice-point count of `𝔭`-elements in
the radius-`r` polydisk is `~ (2r)^{φ(n)}/p` — doubly-exponential in `μ`, astronomically larger than the actual
`W_r`. The gap (Minkowski estimate ≫ true `W_r ≤ slack`) is exactly the equidistribution = the BGK wall.

## What this file PROVES (axiom-clean): the onset is below the saddle at prize scale

Taking the measured `r_0 ≈ p^{1/φ(n)}` (≤ `2·p^{1/φ(n)}` generously), the arithmetic consequence at the prize
parameters is unconditional. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetGrowthLaw

open Real

/-- **The Minkowski/onset exponent is below 1 at prize scale.** `158 / 2^29 < 1`, so the onset scale
`p^{1/φ(n)} = 2^{158/2^29} < 2^1 = 2` for the prize `p ≈ 2^158`, `φ(n) = 2^29`. -/
theorem onset_exponent_lt_one : (158 : ℝ) / (2 ^ 29) < 1 := by
  rw [div_lt_one (by positivity)]
  norm_num

/-- **The onset scale `p^{1/φ(n)} < 2` at prize scale.** From `158/2^29 < 1` and `2 > 1`,
`(2^158)^{1/2^29} = 2^{158/2^29} < 2^1 = 2`. -/
theorem onset_scale_lt_two : (2 : ℝ) ^ ((158 : ℝ) / (2 ^ 29)) < 2 := by
  have h1 : (2 : ℝ) ^ ((158 : ℝ) / (2 ^ 29)) < (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr onset_exponent_lt_one
  simpa using h1

/-- **★ The onset is BELOW the saddle at prize scale.** With the measured law `r_0 ≈ p^{1/φ(n)}` (bounded by
`2·p^{1/φ(n)} < 4`) and the saddle depth `r* = ln p ≈ 109.5` for `p = 2^158`, the onset `r_0 < 4 ≪ r* ≈ 110`.
So the "no wraparound below the saddle" mechanism FAILS at prize scale; the prize is the quantitative
`W_r ≤ slack`, not `r_0 > log p`. We state the clean separation `2·(onset scale) < ln(2^158)`. -/
theorem onset_below_saddle :
    2 * (2 : ℝ) ^ ((158 : ℝ) / (2 ^ 29)) < Real.log (2 ^ 158) := by
  have hupper : 2 * (2 : ℝ) ^ ((158 : ℝ) / (2 ^ 29)) < 4 := by
    have := onset_scale_lt_two; linarith
  have hlog : (4 : ℝ) ≤ Real.log (2 ^ 158) := by
    rw [Real.log_pow]
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    push_cast
    linarith
  exact lt_of_lt_of_le hupper hlog

end ArkLib.ProximityGap.Frontier.OnsetGrowthLaw

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetGrowthLaw.onset_exponent_lt_one
#print axioms ArkLib.ProximityGap.Frontier.OnsetGrowthLaw.onset_scale_lt_two
#print axioms ArkLib.ProximityGap.Frontier.OnsetGrowthLaw.onset_below_saddle
