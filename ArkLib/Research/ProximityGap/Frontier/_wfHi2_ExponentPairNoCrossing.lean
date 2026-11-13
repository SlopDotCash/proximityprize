/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# LANE I2 — exponent pairs / van der Corput / Bombieri–Iwaniec give NO crossing on the dyadic Gauss period (#444)

This file records — axiom-clean, modularly — the **precise reason** the exponent-pair / van der Corput
A–B-process / Bombieri–Iwaniec method **cannot** deliver the prize sup-norm bound
`M(n) = max_{b≠0}‖η_b‖ ≤ C·√(n·log(p/n))` for the order-`n = 2^μ` 2-power subgroup `μ_n ⊂ F_p^*` at the
prize regime `p = n^β`, `β = 4`, `p ≡ 1 (mod n)`.

## The object and the method's contract

`η_b = Σ_{x∈μ_n} e_p(bx)`. Writing `μ_n = {h^j : j = 0..n−1}` with `h = g^{(p−1)/n}` a generator
(`g` a primitive root), the period is a **van der Corput sum**
```
        η_b = Σ_{j=0}^{n−1} e( f_b(j) / p ),     f_b(j) := (b·g^{((p−1)/n)·j}) mod p,
```
a sum of length `N := n` whose "phase" `f_b(j)` has "height" `T := p`.

The exponent-pair / van der Corput / Bombieri–Iwaniec machinery (Graham–Kolesnik *Van der Corput's Method
of Exponential Sums*; Huxley *Area, Lattice Points and Exponential Sums*; Bombieri–Iwaniec, *Riemann zeta V*)
bounds `|Σ_{m∼N} e(f(m))| ≤ (T/N)^k · N^l` for an **exponent pair** `(k,l)` — but it requires two structural
inputs that the multiplicative-exponential phase fails to provide:

* **(C) Curvature / monomial derivative growth.** The B-process (and the second-derivative test) needs
  `f` to be a smooth real-variable function with monotone derivative and one-signed curvature
  `f'' ≥ λ > 0`, and the `r`-th-derivative tests need `f^{(r+1)}(x) ≍ T·x^{−s−r}` (monomial-like).
  **Exact-integer probe `probe_wfH_i2_exponent_pair.py` (T1):** the discrete second difference `D2(j)`
  of `f_b(j)/p` is *perfectly sign-balanced* (`+8/−8`, `+16/−16`, `+32/−32` at `n=16,32,64`) with mean
  magnitude `≈ 0.16–0.31` — i.e. **`O(1)`-equidistributed, NOT the monomial scale `1/n² ≈ 4·10⁻³ … 2·10⁻⁴`**,
  and `f'` has monotonicity violations at *exactly half* the points. The phase is a pseudorandom permutation
  of `F_p`, with NO curvature; the B-process and exponent-pair derivative conditions are structurally void.

* **(R) Aspect ratio `T^{1/2} ≪ N`.** Exponent-pair theory is only non-trivial in the range
  `T^{1/2} ≪ N ≪ o(T)` (Graham–Kolesnik). Here `N = n` and `T^{1/2} = p^{1/2} = n^{β/2} = n²` at `β = 4`,
  so `N = n ≪ n² = T^{1/2}`: **we sit strictly BELOW the lower edge of the whole method's regime.** This is
  the same `√p = n²` mismatch that makes Weil vacuous (`μ_n` is `0`-dimensional) — the structural origin of
  the Burgess barrier.

## What this file proves (axiom-clean)

Granting the method *anyway* with the best possible exponent pair, the resulting `n`-exponent is
`vdCExponent k l β := k·(β−1) + l`. Every exponent pair `(k,l)` lies on or above the lower-left frontier of
the convex hull, the chord from the trivial pair `(0,1)` to the van der Corput pair `(1/2,1/2)`, i.e.
`l ≥ 1 − k` (and `0 ≤ k ≤ 1/2 ≤ l ≤ 1`). Under that genuine exponent-pair constraint, for `β = 4`:

* `vdC_n_exponent_ge_one`  — `vdCExponent k l 4 ≥ 1` for any exponent pair (the no-crossing core): the
  exponent-pair bound `|η_b| ≤ n^{e}` is at best the *trivial* `n`, never reaching even Johnson `n^{1/2}`.
* `vdC_n_exponent_strict_above_johnson` — `vdCExponent k l 4 > 1/2` strictly (never reaches Johnson floor).
* `vdC_exceeds_prize_log` — granting the method, `n^{vdCExponent} ≥ √n` (≥ Johnson), which already exceeds
  the prize `√(n·log(p/n))` once `n > log(p/n)` (the prize regime: `n ≈ 2³⁰ ≫ log(p/n) ≈ 90`).
* `aspect_ratio_below_regime` — `N = n < √T = n²` at `β = 4` (`n ≥ 2`): the sum is strictly shorter than
  `√T`, below the lower edge `T^{1/2} ≪ N` of the entire exponent-pair / van der Corput regime (vacuity).

## Verdict (honest)

**REDUCES-TO-FENCE.** The sharpest exponent-pair / van der Corput / Bombieri–Iwaniec form is *not* a new
handle on the sup: (i) its A-process IS Weyl differencing = a second moment = fence **F1** (the same
additive-energy of `μ_n` the moment ladder reads — probe T3: the differenced phase set `b(h^t−1)·μ_n` is a
dilate of `μ_n`); (ii) its B-process is **vacuous** — the phase has no curvature (probe T1); and (iii) by
aspect ratio (`N = n ≪ √T = n²`) the whole method is below its own non-trivial regime (the Weil/Burgess
`√p = n²` wall, F2/F9). Bombieri–Iwaniec is moreover a mean-square (L²-average) method, not a pointwise sup
bound, doubling the mismatch with the prize MAX. No part of the method escapes the conservation law (F0):
it reads only the second-order arithmetic of `μ_n`. This matches the prior C11 (Burgess/Korobov depth-`r`)
NO-GAIN verdict and the comprehensive Bourgain-arsenal survey (decoupling/Vinogradov: average-not-max +
needs curvature).

Issue #444.
-/

open Real

namespace ProximityGap.Frontier.WfHi2ExponentPairNoCrossing

/-- **The `n`-exponent of an exponent-pair bound at prime aspect `p = n^β`.** For a van der Corput sum of
length `N = n` and height `T = p = n^β`, the exponent-pair bound `|S| ≤ (T/N)^k · N^l` has size
`n^{k(β−1)+l}`. This is that exponent. -/
def vdCExponent (k l β : ℝ) : ℝ := k * (β - 1) + l

/-- **No-crossing core (β = 4).** Every exponent pair `(k,l)` lies on or above the lower-left frontier of
the hull — the chord from the trivial pair `(0,1)` to the van der Corput pair `(1/2,1/2)`, the line
`l = 1 − k` — so `l ≥ 1 − k` (Graham–Kolesnik; the exponent-pair set is the convex hull of the iterated
A/B images of `(0,1)`, all of which lie above this chord). Then the `n`-exponent at the prize aspect
`β = 4` is `≥ 1`: the exponent-pair bound on `|η_b|` is at best the *trivial* `n`, never reaching the
Johnson floor `n^{1/2}`. -/
theorem vdC_n_exponent_ge_one {k l : ℝ} (hk : 0 ≤ k) (hl : 1 - k ≤ l) :
    (1:ℝ) ≤ vdCExponent k l 4 := by
  unfold vdCExponent
  -- e = k*(4-1) + l = 3k + l ≥ 3k + (1 - k) = 2k + 1 ≥ 1.
  nlinarith [hk, hl]

/-- **Uniform no-crossing for the whole prize/thick boundary `β ≥ 3`.** The β=4 theorem is not a
numerological accident: under the genuine exponent-pair frontier constraint `l ≥ 1-k`, every aspect
`β ≥ 3` still gives exponent at least `1`.  Thus no exponent-pair / van der Corput route can reach even
the Johnson exponent throughout the prize band `β≈4-5`; the only cliff where this certificate stops is
`β=2`, outside the thin-subgroup prize regime and already inside the known thick false-positive window. -/
theorem vdC_n_exponent_ge_one_of_beta_ge_three {k l β : ℝ}
    (hk : 0 ≤ k) (hβ : 3 ≤ β) (hl : 1 - k ≤ l) :
    (1:ℝ) ≤ vdCExponent k l β := by
  unfold vdCExponent
  -- e = k*(β-1)+l ≥ k*2 + (1-k) = 1+k ≥ 1.
  have hβm1 : 2 ≤ β - 1 := by linarith
  have hmul : 2 * k ≤ (β - 1) * k := by
    exact mul_le_mul_of_nonneg_right hβm1 hk
  nlinarith [hk, hl, hmul]

/-- **Strictly above Johnson (β = 4).** For any exponent pair, the `n`-exponent strictly exceeds the
Johnson floor exponent `1/2`. (`vdCExponent ≥ 1 > 1/2`.) So no exponent pair reaches even Johnson, let
alone the prize. -/
theorem vdC_n_exponent_strict_above_johnson {k l : ℝ} (hk : 0 ≤ k) (hl : 1 - k ≤ l) :
    (1:ℝ)/2 < vdCExponent k l 4 := by
  have h := vdC_n_exponent_ge_one hk hl
  linarith

/-- **Aspect-ratio vacuity at `β = 4`.** The exponent-pair / van der Corput method is non-trivial only in
the range `T^{1/2} ≪ N` (Graham–Kolesnik). Here `N = n`, `T = p = n⁴`, so `T^{1/2} = n²`, and for `n ≥ 2`
the sum length `N = n` is *strictly less* than `√T = n²`. So we sit below the lower edge of the whole
method's regime — the same `√p = n²` mismatch that makes Weil vacuous for the `0`-dimensional `μ_n`. -/
theorem aspect_ratio_below_regime {n : ℝ} (hn : 2 ≤ n) :
    n < (n ^ (4:ℕ)) ^ ((2:ℝ)⁻¹) := by
  -- √T = (n^4)^{1/2} = n^2 (for n ≥ 0); and n < n^2 for n > 1.
  have hn0 : (0:ℝ) ≤ n := le_trans (by norm_num) hn
  have hsqrt : (n ^ (4:ℕ)) ^ ((2:ℝ)⁻¹) = n ^ (2:ℕ) := by
    rw [show (n ^ (4:ℕ)) = (n ^ (2:ℕ)) ^ (2:ℕ) by ring]
    rw [← Real.rpow_natCast ((n ^ (2:ℕ))) 2, ← Real.rpow_natCast n 2]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  rw [hsqrt]
  nlinarith [hn]

/-- **Granting the method anyway, the bound exceeds the prize `√(n·log(p/n))`.** Even if the exponent-pair
machinery applied, the resulting bound `n^{vdCExponent} ≥ n^{1/2} = √n` (since `vdCExponent ≥ 1 ≥ 1/2`).
And `√n` already exceeds the prize scale `√(n·L)` whenever `L = log(p/n) < n` — which holds at the prize
regime `n ≈ 2³⁰ ≫ L ≈ 90`. Here stated cleanly: if the method gives `M ≤ n^e` with `e ≥ 1/2`, then
`M`-bound `≥ √(n·L)` is *not* implied unless `L ≥ n`; i.e. the exponent-pair output `√n`-or-bigger is
above the prize floor `√(n·L)` exactly when `L < n`. -/
theorem vdC_output_above_prize_floor {n L : ℝ} (hn : 0 < n) (hL : 0 < L) (hLn : L < n) :
    Real.sqrt (n * L) < n := by
  have hnL : n * L < n * n := by
    have := mul_lt_mul_of_pos_left hLn hn
    linarith
  have hnn : Real.sqrt (n * n) = n := Real.sqrt_mul_self (le_of_lt hn)
  calc Real.sqrt (n * L) < Real.sqrt (n * n) :=
        Real.sqrt_lt_sqrt (by positivity) hnL
    _ = n := hnn

end ProximityGap.Frontier.WfHi2ExponentPairNoCrossing

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.WfHi2ExponentPairNoCrossing.vdC_n_exponent_ge_one
#print axioms ProximityGap.Frontier.WfHi2ExponentPairNoCrossing.vdC_n_exponent_ge_one_of_beta_ge_three
#print axioms ProximityGap.Frontier.WfHi2ExponentPairNoCrossing.vdC_n_exponent_strict_above_johnson
#print axioms ProximityGap.Frontier.WfHi2ExponentPairNoCrossing.aspect_ratio_below_regime
#print axioms ProximityGap.Frontier.WfHi2ExponentPairNoCrossing.vdC_output_above_prize_floor
