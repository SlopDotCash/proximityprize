/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The ensemble ramp-defect law at depth j = 3 (#466, lane S6)

Companion to `_JacobiRampDefectLaw.lean` (j = 1 unconditional, j = 2 conditional on clean
`E₂`/`T₃`). This file extends the ensemble Jacobi ramp-defect law to depth `j = 3` via the
**Hankel-determinant route** `b_k² = D_k · D_{k-2} / D_{k-1}²` (with `D₋₁ = D₀ = 1`), the same
identity the round-2 verifier validated for `j = 2`.

## Setup (unchanged from the j = 1, 2 file)

`η_b = Σ_{x∈μ_n} e_p(bx)`, `b ≠ 0`, `n` even so `-1 ∈ μ_n` and `η_b ∈ ℝ`; `μ_emp` = uniform
measure on the `m = (p-1)/n` Gauss-period values. The raw moments `M_k` are exact rationals in
`(n, p)` and the counting inputs `E_r` (additive `2r`-energy) and `T_{2r+1}` (odd zero-sum
counts):

* `M₁ = -n/(p-1)`, `M₂ = n(p-n)/(p-1)` (unconditional);
* `M₃ = (p·T₃ - n³)/(p-1)`, `M₄ = (p·E₂ - n⁴)/(p-1)` (clean `T₃ = 0`, `E₂ = 3n²-3n`);
* **new at depth 3:** `M₅ = (p·T₅ - n⁵)/(p-1)`, `M₆ = (p·E₃ - n⁶)/(p-1)`, with the CLEAN
  inputs `T₅ = 0` and `E₃ = 15n³-45n²+40n` (the char-0 Gaussian 6-energy; leading `5‼ = 15`).

The measure is neither centered nor even, so the Jacobi off-diagonals are computed from the
CENTRAL-moment Hankel determinants
`D₂ = c₂c₄ - c₃² - c₂³`, `D₃ = -c₂³c₆ + 2c₂²c₃c₅ + c₂²c₄² - 3c₂c₃²c₄ + c₂c₄c₆ - c₂c₅² + c₃⁴
- c₃²c₆ + 2c₃c₄c₅ - c₄³` (the standard `4×4` centered Hankel expansion), and `b₃² = D₃c₂/D₂²`.
Because `b_k²` is translation-invariant, this reproduces the raw-moment Jacobi coefficients
exactly (validated in `scripts/probes/probe_466_jacobi_ramp_j3.py`: `b₁²`, `b₂²` reproduce the
j = 1, 2 file; float64 Lanczos on the actual Gauss-period spectrum matches the closed forms to
`≤ 3.7e-16` for `n ∈ {8,16,32}`, `β ≥ 4`, three generic primes each).

## The laws (proved below; symbolically + numerically validated in the probe)

* `b3sq_closed` (CONDITIONAL on clean `E₃`, `T₅ = 0`):
  `b₃² = (p-1-n)·(p·A + B) / ((2n-3)p - (n³-3))²` with
  `A = 12n³-72n²+143n-93`, `B = -2n⁶+9n⁵-21n⁴+50n³-54n²-54n+93`.
  The denominator base `(2n-3)p - (n³-3)` is the SAME factor carried by `b₂²`.
* `oneMinusQ3_exact`: `1 - q₃ = 1 - b₃²/(3n) = N₃(n,p) / (3n·((2n-3)p-(n³-3))²)` with `N₃` the
  degree-`(7,2)` numerator recorded below.
* `oneMinusQ3_floor_split`: `1 - q₃ = (18n-31)/(3n(2n-3)) + R₃(n,p)` — the depth-3 defect
  carries the **char-0 Gaussian floor `F₃ = (18n-31)/(3n(2n-3)) ≈ 3/n`** (double the j = 2
  floor `3/(2n)`) plus a positive `p`-ramp `R₃` with leading coefficient
  `G₃ = (n-2)(2n⁴-17n³+53n²-66n+29)/(3(2n-3)²)`.

## The crossover depth j*(n,p) — the point of the lane

Write `1 - q_j = F_j(n) + R_j(n,p)` with `F_j` the char-0 floor (the `p → ∞` limit; an `n`-only
rational) and `R_j > 0` the finite-`p` ramp. The Jacobi window at depth `j` is *`n`-dominated*
iff `F_j ≥ R_j`, else *`p`-dominated* (the char-`p` ramp controls it). Define
`j*(n,p) := min{ j : F_j(n) ≥ R_j(n,p) }`.

* **`j = 1` is always `p`-dominated:** `F₁ = 0` (the j = 1 defect `(n-1)/(p-1) + n/(p-1)²` has
  no `n`-only term — it "reads `p` only") while `R₁ = 1 - q₁ > 0` (`crossover_j1_p_dominated`).
* **`j = 2` is `n`-dominated in regime:** `F₂ = 3/(2n) ≥ R₂` exactly when
  `n(n-2)²(p-1) + n²(2n-3) ≤ 3(p-1-n)²` (`crossover_j2_iff`), which holds for every `p ≥ n³`
  (hence every prize prime `p ≥ n⁴`; `crossover_j2_of_regime`).

So **`j*(n,p) = 2` for all prize primes**: the char-`p` ramp controls the Jacobi ramp defect at
*exactly one* depth, `j = 1`; from `j = 2` onward the char-0 Gaussian floor dominates. This is
the first quantitative statement of WHERE (which Jacobi depth) the char-`p` defect ceases to
control the window. (The probe reports the exact per-`n` crossover primes: `n=8: p>115`,
`n=16: p>1081`, `n=32: p>9667` — all `≪ n⁴`.)

## HONESTY

These identities pin the ensemble MEAN ramp only (the `j = 1,2,3` Jacobi off-diagonals of the
full spectral measure — equivalently the first three Hankel determinants, moments up to `E₃`).
The clean-energy inputs `T₃ = 0`, `E₂ = 3n²-3n`, **`T₅ = 0`**, `E₃ = 15n³-45n²+40n` are NAMED
hypotheses — generically true but false at structured primes: the probe finds the Fermat prime
`p = 65537` (`n = 16`) has `T₅ = 80 ≠ 0` (while `E₃` stays clean), so the FIRST clean-input
carrier that a resonant prime breaks at depth 3 is `T₅`. The instance turnover `k*(instance)`,
the worst-`b` sup-norm, and the char-`p` defect at deeper `j` (where `E₃` itself deviates) all
stay OPEN. The crossover `j*(n,p) = 2` describes the ensemble-mean ramp under the clean inputs,
NOT the instance. This brick is exact bookkeeping at the shallow end, NOT progress on the wall.
Issue #466.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3

/-! ## Regime facts: denominator positivity from `2 ≤ n` and `n³ ≤ p` -/

/-- In the regime `2 ≤ n`, `n³ ≤ p` the shared denominator base `(2n-3)p - (n³-3)` is positive.
(`b₂²` and `b₃²` share this factor; for `b₃²` it must be nonzero, unlike the milder `p-1-n`
of `b₁²`, `b₂²`.) -/
theorem denomBase_pos {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) :
    0 < (2 * n - 3) * p - (n ^ 3 - 3) := by
  nlinarith [hp3, hn, sq_nonneg (n - 2), mul_le_mul_of_nonneg_left hp3 (by linarith : (0:ℝ) ≤ 2 * n - 3)]

/-- The regime `2 ≤ n`, `n³ ≤ p` implies `n < p - 1` (so the variance `c₂ > 0`). -/
theorem lt_pMinusOne {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) : n < p - 1 := by
  nlinarith [hp3, hn, sq_nonneg n, sq_nonneg (n - 1)]

/-! ## j = 3: the closed form of the third Jacobi off-diagonal (Hankel-determinant route) -/

/-- **The depth-3 Jacobi off-diagonal, closed form** (clean regime `T₃ = T₅ = 0`,
`E₂ = 3n²-3n`, `E₃ = 15n³-45n²+40n`). Computed via the Hankel-determinant identity
`b₃² = D₃ c₂ / D₂²` with `D₂`, `D₃` the `3×3` and `4×4` centered-moment Hankel determinants.
Result:
`b₃² = (p-1-n)·(p·(12n³-72n²+143n-93) + (-2n⁶+9n⁵-21n⁴+50n³-54n²-54n+93)) / ((2n-3)p-(n³-3))²`. -/
theorem b3sq_closed (n p m1 m2 m3 m4 m5 m6 c2 c3 c4 c5 c6 D2 D3 b3sq : ℝ)
    (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hm5 : m5 = -(n ^ 5) / (p - 1))
    (hm6 : m6 = ((15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * p - n ^ 6) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hc5 : c5 = m5 - 5 * m1 * m4 + 10 * m1 ^ 2 * m3 - 10 * m1 ^ 3 * m2 + 4 * m1 ^ 5)
    (hc6 : c6 = m6 - 6 * m1 * m5 + 15 * m1 ^ 2 * m4 - 20 * m1 ^ 3 * m3
                  + 15 * m1 ^ 4 * m2 - 5 * m1 ^ 6)
    (hD2 : D2 = c2 * c4 - c3 ^ 2 - c2 ^ 3)
    (hD3 : D3 = -c2 ^ 3 * c6 + 2 * c2 ^ 2 * c3 * c5 + c2 ^ 2 * c4 ^ 2 - 3 * c2 * c3 ^ 2 * c4
                  + c2 * c4 * c6 - c2 * c5 ^ 2 + c3 ^ 4 - c3 ^ 2 * c6 + 2 * c3 * c4 * c5 - c4 ^ 3)
    (hb3 : b3sq = D3 * c2 / D2 ^ 2) :
    b3sq = (p - 1 - n) * (p * (12 * n ^ 3 - 72 * n ^ 2 + 143 * n - 93)
             + (-2 * n ^ 6 + 9 * n ^ 5 - 21 * n ^ 4 + 50 * n ^ 3 - 54 * n ^ 2 - 54 * n + 93))
           / ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2 := by
  have hnp : n < p - 1 := lt_pMinusOne hn hp3
  have hn0 : (0 : ℝ) < n := by linarith
  have hp0 : (0 : ℝ) < p := by nlinarith [hp3, hn0]
  have hP0 : (0 : ℝ) < p - 1 := by linarith
  have hQ0 : (0 : ℝ) < p - 1 - n := by linarith
  have hR0 : (0 : ℝ) < (2 * n - 3) * p - (n ^ 3 - 3) := denomBase_pos hn hp3
  have hP : p - 1 ≠ 0 := ne_of_gt hP0
  have hn' : n ≠ 0 := ne_of_gt hn0
  subst hm1 hm2 hm3 hm4 hm5 hm6
  -- closed form of the variance, and its nonvanishing
  have hc2v : c2 = n * p * (p - 1 - n) / (p - 1) ^ 2 := by rw [hc2]; field_simp; ring
  have hc2pos : 0 < c2 := by
    rw [hc2v]; exact div_pos (mul_pos (mul_pos hn0 hp0) hQ0) (pow_pos hP0 2)
  have hc2ne : c2 ≠ 0 := ne_of_gt hc2pos
  -- closed form of the 3×3 Hankel determinant D₂, and its nonvanishing
  have hD2v : D2 = n ^ 2 * p ^ 2 * ((2 * n - 3) * p - (n ^ 3 - 3)) / (p - 1) ^ 3 := by
    rw [hD2, hc2, hc3, hc4]; field_simp; ring
  have hD2pos : 0 < D2 := by
    rw [hD2v]
    exact div_pos (mul_pos (mul_pos (pow_pos hn0 2) (pow_pos hp0 2)) hR0) (pow_pos hP0 3)
  have hD2ne : D2 ≠ 0 := ne_of_gt hD2pos
  -- closed form of the 4×4 Hankel determinant D₃
  have hD3v : D3 = n ^ 3 * p ^ 3 * (p * (12 * n ^ 3 - 72 * n ^ 2 + 143 * n - 93)
                    + (-2 * n ^ 6 + 9 * n ^ 5 - 21 * n ^ 4 + 50 * n ^ 3 - 54 * n ^ 2 - 54 * n + 93))
                  / (p - 1) ^ 4 := by
    rw [hD3, hc2, hc3, hc4, hc5, hc6]; field_simp; ring
  -- assemble b₃² = D₃ c₂ / D₂²
  rw [hb3, hD3v, hc2v, hD2v]
  rw [div_pow]
  have hRne : (2 * n - 3) * p - (n ^ 3 - 3) ≠ 0 := ne_of_gt hR0
  field_simp

/-! ## j = 3: the ramp-defect law and its char-0 floor split -/

/-- **The j = 3 ensemble ramp-defect law** (clean regime):
`1 - q₃ = 1 - b₃²/(3n) = N₃(n,p) / (3n·((2n-3)p-(n³-3))²)`, where `N₃` is the degree-`(7,2)`
numerator below. Leading behaviour `(18n-31)/(3n(2n-3)) + G₃/(p-1) + O(1/(p-1)²)`. -/
theorem oneMinusQ3_exact (n p m1 m2 m3 m4 m5 m6 c2 c3 c4 c5 c6 D2 D3 b3sq : ℝ)
    (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hm5 : m5 = -(n ^ 5) / (p - 1))
    (hm6 : m6 = ((15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * p - n ^ 6) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hc5 : c5 = m5 - 5 * m1 * m4 + 10 * m1 ^ 2 * m3 - 10 * m1 ^ 3 * m2 + 4 * m1 ^ 5)
    (hc6 : c6 = m6 - 6 * m1 * m5 + 15 * m1 ^ 2 * m4 - 20 * m1 ^ 3 * m3
                  + 15 * m1 ^ 4 * m2 - 5 * m1 ^ 6)
    (hD2 : D2 = c2 * c4 - c3 ^ 2 - c2 ^ 3)
    (hD3 : D3 = -c2 ^ 3 * c6 + 2 * c2 ^ 2 * c3 * c5 + c2 ^ 2 * c4 ^ 2 - 3 * c2 * c3 ^ 2 * c4
                  + c2 * c4 * c6 - c2 * c5 ^ 2 + c3 ^ 4 - c3 ^ 2 * c6 + 2 * c3 * c4 * c5 - c4 ^ 3)
    (hb3 : b3sq = D3 * c2 / D2 ^ 2) :
    1 - b3sq / (3 * n)
      = (n ^ 7 + 2 * n ^ 6 * p + 7 * n ^ 6 - 21 * n ^ 5 * p - 12 * n ^ 5 + 51 * n ^ 4 * p
          + 11 * n ^ 4 - 110 * n ^ 3 * p - 4 * n ^ 3 + 36 * n ^ 2 * p ^ 2 + 161 * n ^ 2 * p
          - 108 * n ^ 2 - 116 * n * p ^ 2 + 50 * n * p + 66 * n + 93 * p ^ 2 - 186 * p + 93)
        / (3 * n * ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2) := by
  have hb3v := b3sq_closed n p m1 m2 m3 m4 m5 m6 c2 c3 c4 c5 c6 D2 D3 b3sq hn hp3
    hm1 hm2 hm3 hm4 hm5 hm6 hc2 hc3 hc4 hc5 hc6 hD2 hD3 hb3
  have hn0 : (0 : ℝ) < n := by linarith
  have hR0 : (0 : ℝ) < (2 * n - 3) * p - (n ^ 3 - 3) := denomBase_pos hn hp3
  have hn' : n ≠ 0 := ne_of_gt hn0
  have hRne : (2 * n - 3) * p - (n ^ 3 - 3) ≠ 0 := ne_of_gt hR0
  rw [hb3v]
  -- keep the denominator base atomic so `field_simp` does not expand `Q²` and lose `Q ≠ 0`
  set D := (2 * n - 3) * p - (n ^ 3 - 3) with hDdef
  field_simp
  rw [hDdef]
  ring

/-- **Floor split at j = 3**: `1 - q₃ = (18n-31)/(3n(2n-3)) + R₃(n,p)`, where the char-0
Gaussian floor `F₃ = (18n-31)/(3n(2n-3)) ≈ 3/n` is present for every `p` (it is the `p → ∞`
limit) and `R₃` is the explicitly-written finite-`p` ramp. Contrast the depths: `j = 1` floor
`0`, `j = 2` floor `3/(2n)`, `j = 3` floor `≈ 3/n` — the char-0 floor grows with depth. -/
theorem oneMinusQ3_floor_split (n p m1 m2 m3 m4 m5 m6 c2 c3 c4 c5 c6 D2 D3 b3sq : ℝ)
    (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p)
    (hm1 : m1 = -n / (p - 1))
    (hm2 : m2 = n * (p - n) / (p - 1))
    (hm3 : m3 = -(n ^ 3) / (p - 1))
    (hm4 : m4 = ((3 * n ^ 2 - 3 * n) * p - n ^ 4) / (p - 1))
    (hm5 : m5 = -(n ^ 5) / (p - 1))
    (hm6 : m6 = ((15 * n ^ 3 - 45 * n ^ 2 + 40 * n) * p - n ^ 6) / (p - 1))
    (hc2 : c2 = m2 - m1 ^ 2)
    (hc3 : c3 = m3 - 3 * m1 * m2 + 2 * m1 ^ 3)
    (hc4 : c4 = m4 - 4 * m1 * m3 + 6 * m1 ^ 2 * m2 - 3 * m1 ^ 4)
    (hc5 : c5 = m5 - 5 * m1 * m4 + 10 * m1 ^ 2 * m3 - 10 * m1 ^ 3 * m2 + 4 * m1 ^ 5)
    (hc6 : c6 = m6 - 6 * m1 * m5 + 15 * m1 ^ 2 * m4 - 20 * m1 ^ 3 * m3
                  + 15 * m1 ^ 4 * m2 - 5 * m1 ^ 6)
    (hD2 : D2 = c2 * c4 - c3 ^ 2 - c2 ^ 3)
    (hD3 : D3 = -c2 ^ 3 * c6 + 2 * c2 ^ 2 * c3 * c5 + c2 ^ 2 * c4 ^ 2 - 3 * c2 * c3 ^ 2 * c4
                  + c2 * c4 * c6 - c2 * c5 ^ 2 + c3 ^ 4 - c3 ^ 2 * c6 + 2 * c3 * c4 * c5 - c4 ^ 3)
    (hb3 : b3sq = D3 * c2 / D2 ^ 2) :
    1 - b3sq / (3 * n)
      = (18 * n - 31) / (3 * n * (2 * n - 3))
        + (2 * n ^ 7 + 4 * n ^ 6 * p - 7 * n ^ 6 - 48 * n ^ 5 * p - 14 * n ^ 5 + 237 * n ^ 4 * p
            + 58 * n ^ 4 - 605 * n ^ 3 * p + 67 * n ^ 3 + 838 * n ^ 2 * p - 390 * n ^ 2
            - 599 * n * p + 456 * n + 174 * p - 174)
          / (3 * (2 * n - 3) * ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2) := by
  have h := oneMinusQ3_exact n p m1 m2 m3 m4 m5 m6 c2 c3 c4 c5 c6 D2 D3 b3sq hn hp3
    hm1 hm2 hm3 hm4 hm5 hm6 hc2 hc3 hc4 hc5 hc6 hD2 hD3 hb3
  rw [h]
  have hn0 : (0 : ℝ) < n := by linarith
  have hR0 : (0 : ℝ) < (2 * n - 3) * p - (n ^ 3 - 3) := denomBase_pos hn hp3
  have h2n3 : (0 : ℝ) < 2 * n - 3 := by linarith
  have hn' : n ≠ 0 := ne_of_gt hn0
  have hRne : (2 * n - 3) * p - (n ^ 3 - 3) ≠ 0 := ne_of_gt hR0
  have h2n3ne : 2 * n - 3 ≠ 0 := ne_of_gt h2n3
  -- combine the two RHS fractions and cross-multiply with EXPLICIT nonzero denominators
  -- (avoids `field_simp` expanding `Q²` and losing the `Q ≠ 0` hypothesis)
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hQ2 : ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2 ≠ 0 := pow_ne_zero 2 hRne
  have hb : (3 : ℝ) * n * (2 * n - 3) ≠ 0 := mul_ne_zero (mul_ne_zero h3 hn') h2n3ne
  have hd : (3 : ℝ) * (2 * n - 3) * ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h3 h2n3ne) hQ2
  have hL : (3 : ℝ) * n * ((2 * n - 3) * p - (n ^ 3 - 3)) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h3 hn') hQ2
  rw [div_add_div _ _ hb hd, div_eq_div_iff hL (mul_ne_zero hb hd)]
  ring

/-! ## The crossover depth j*(n,p): where the char-p defect stops controlling the window -/

/-- **j = 1 is always `p`-dominated.** The char-0 floor of the j = 1 defect is `F₁ = 0` (the
defect `1 - q₁ = (n-1)/(p-1) + n/(p-1)²` has NO `n`-only term — it "reads `p` only"), while the
ramp `R₁ = 1 - q₁` is strictly positive. So the char-`p` ramp is the ENTIRE j = 1 defect: at
depth 1 the window is `p`-dominated for every prime. -/
theorem crossover_j1_p_dominated {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) :
    (0 : ℝ) < (n - 1) / (p - 1) + n / (p - 1) ^ 2 := by
  have hnp : n < p - 1 := lt_pMinusOne hn hp3
  have hP0 : (0 : ℝ) < p - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have t1 : (0 : ℝ) < (n - 1) / (p - 1) := div_pos (by linarith) hP0
  have t2 : (0 : ℝ) < n / (p - 1) ^ 2 := div_pos hn0 (pow_pos hP0 2)
  linarith

/-- **Exact crossover characterization at j = 2.** The char-0 floor `F₂ = 3/(2n)` dominates the
j = 2 ramp `R₂ = ((n-2)²(p-1) + n(2n-3))/(2(p-1-n)²)` — i.e. `R₂ ≤ F₂` — **iff**
`n(n-2)²(p-1) + n²(2n-3) ≤ 3(p-1-n)²`. (`R₂` is the ramp from `_JacobiRampDefectLaw`'s
`oneMinusQ2_exceeds_floor`.) -/
theorem crossover_j2_iff {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) :
    ((n - 2) ^ 2 * (p - 1) + n * (2 * n - 3)) / (2 * (p - 1 - n) ^ 2) ≤ 3 / (2 * n)
      ↔ n * (n - 2) ^ 2 * (p - 1) + n ^ 2 * (2 * n - 3) ≤ 3 * (p - 1 - n) ^ 2 := by
  have hnp : n < p - 1 := lt_pMinusOne hn hp3
  have hn0 : (0 : ℝ) < n := by linarith
  have hQ0 : (0 : ℝ) < p - 1 - n := by linarith
  have hden1 : (0 : ℝ) < 2 * (p - 1 - n) ^ 2 := by positivity
  have hden2 : (0 : ℝ) < 2 * n := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The j = 2 crossover holds in the whole regime `n³ ≤ p`** (hence at every prize prime
`p ≥ n⁴`): `n(n-2)²(p-1) + n²(2n-3) ≤ 3(p-1-n)²`, i.e. `R₂ ≤ F₂`. Combined with
`crossover_j1_p_dominated`, this gives the crossover depth **`j*(n,p) = 2`**: the char-`p`
ramp controls the Jacobi ramp defect at exactly one depth, `j = 1`; from `j = 2` the char-0
Gaussian floor `3/(2n)` dominates. -/
theorem crossover_j2_of_regime {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) :
    n * (n - 2) ^ 2 * (p - 1) + n ^ 2 * (2 * n - 3) ≤ 3 * (p - 1 - n) ^ 2 := by
  -- certificate: 3(p-1-n)² - RHS = 3(p-n³)² + (5n³+4n²-10n-6)(p-n³) + f(n³), all terms ≥ 0
  have hpn3 : (0 : ℝ) ≤ p - n ^ 3 := by linarith
  have hlin : (0 : ℝ) ≤ 5 * n ^ 3 + 4 * n ^ 2 - 10 * n - 6 := by nlinarith [hn, sq_nonneg n]
  have hf0 : (0 : ℝ) ≤ 2 * n ^ 6 + 4 * n ^ 5 - 10 * n ^ 4 - 7 * n ^ 3 + 2 * n ^ 2 + 10 * n + 3 := by
    nlinarith [hn, sq_nonneg n, sq_nonneg (n - 2), pow_pos (by linarith : (0:ℝ) < n) 4]
  nlinarith [sq_nonneg (p - n ^ 3), mul_nonneg hpn3 hlin, hf0, hpn3]

/-- **The crossover, stated as `R₂ ≤ F₂` directly** (the ramp does not exceed the char-0 floor at
j = 2 in the regime). Packaged form of `crossover_j2_iff` ∘ `crossover_j2_of_regime`. -/
theorem crossover_j2_ramp_le_floor {n p : ℝ} (hn : 2 ≤ n) (hp3 : n ^ 3 ≤ p) :
    ((n - 2) ^ 2 * (p - 1) + n * (2 * n - 3)) / (2 * (p - 1 - n) ^ 2) ≤ 3 / (2 * n) :=
  (crossover_j2_iff hn hp3).mpr (crossover_j2_of_regime hn hp3)

end ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.denomBase_pos
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.b3sq_closed
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.oneMinusQ3_exact
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.oneMinusQ3_floor_split
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.crossover_j1_p_dominated
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.crossover_j2_iff
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.crossover_j2_of_regime
#print axioms ArkLib.ProximityGap.Frontier.JacobiRampDefectLawJ3.crossover_j2_ramp_le_floor
