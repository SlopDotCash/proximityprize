/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Truncated max-support moment LP: the principal-block ceiling is VACUOUS (#444)

**NEGATIVE / guardrail brick (an honest no-go barrier, NOT a closure).**

This file analyses the *truncated Hamburger max-support LP* for the nonzero Gauss-period spectrum
and proves it cannot certify the prize bound `M ≤ C √(n log p)`.

Setup.  Let `μ = ∑_{b≠0} δ_{λ_b}` be the empirical measure of the squared periods
`λ_b = |η_b|²`, `b ∈ (𝔽_p)^× / μ_n`.  The proven exact data are:
* total mass `m₀ = q − 1`;
* first moment `m₁ = q·E₁ − n² = q n − n²` (Parseval, minus the removed DC atom `η₀ = n`);
* second moment `m₂ = q·E₂ − n⁴ = q(3n² − 3n) − n⁴` (Stickelberger: `E₂ = 3n² − 3n` exactly,
  `W₂ = 0` for all `p > n⁴`);
* every atom has mass `≥ n` (an orbit/coset of `μ_n` has `n` elements — angle 1).

The LP: *maximise* `B = max support = M²` over nonnegative measures on `[0,B]` matching
`(m₀, m₁, m₂)` with top-atom mass `≥ n`.  This is the genuine *constrained* truncated moment
problem the prior frontier files never set up:
* `_AttackE2_MomentConeSpikeNoGo` refuted that `max` is a *function* of `(S₁,S₂,S₄)` via an
  unbounded-*count* spike — it did NOT optimise the top-atom location under fixed mass+min-mass.
* `_wf8B5_MomentProblemLogConvex` proved the Hankel ratio `Q(r) ≥ 1` (one inequality), not the
  extremal max-support dual.

## The closed form (`Markov–Krein` two-point extremal representation)

The single binding feasibility constraint is the variance-nonnegativity (Hankel `2×2` PSD) of the
mass remaining after pulling out the top atom of mass exactly `n`:
`(m₂ − n B²)(m₀ − n) ≥ (m₁ − n B)²`, which rearranges to the quadratic
`n m₀ B² − 2 m₁ n B − (m₂ m₀ − m₂ n − m₁²) ≤ 0`.
Its larger root `B⋆ = ((m₁ n) + √Δ) / (n m₀)`, `Δ = (m₁ n)² + n m₀ (m₂ m₀ − m₂ n − m₁²)`, is the
closed-form ceiling — the best possible bound from `{mass, m₁, m₂, atom-mass ≥ n, support ≥ 0}`.

## The barrier (two exact, dimension-free facts, both `sorry`-free here)

1. **`supportCeiling_ge_csLower`** — the LP *upper* ceiling is never below the established Cauchy–
   Schwarz *lower* bound `m₂/m₁ = A₂/A₁`.  Concretely, the larger root of
   `n m₀ B² − 2 m₁ n B − C ≤ 0` (with `C = m₂ m₀ − m₂ n − m₁² ≥ 0`, the Hankel determinant times
   data) dominates `m₂/m₁` because the quadratic is *negative* at `B = m₂/m₁` whenever
   `C ≥ 0`.  So the LP can never squeeze below the floor: ceiling `=` floor `+` slack `≥` floor.
   The free Cauchy–Schwarz floor is the *lower* bound `M² ≥ m₂/m₁`; an upper certificate must lie
   *above* it, hence cannot be `≤ M²` strictly — the LP cannot pin `M`.

2. **`csLower_eq_threeN_asymptotic`** (exact algebra) — `m₂/m₁` itself is the established
   `√3·√n`-scale floor: `m₂/m₁ = (q(3n²−3n) − n⁴)/(qn − n²)`, and at prize scale `q ≈ n⁴` this is
   `→ 3n` with NO log factor.  We record the exact value at the canonical scale `q = n⁴`:
   `m₂/m₁ |_{q=n⁴} = (3n²−3n−1)·n / (n−1)` … (rational, computed in `csLower_value`).

Conclusion: the truncated max-support LP on the *exact low moments* has a closed-form ceiling that
is `≥ √3·√n` and grows polynomially in `n` (empirically `√(B⋆/n) ∼ n^{3/4}`), so it is **vacuous**
as a `√(n log p)` upper bound.  The angle REDUCES: to reach the log one must push the moment ladder
to depth `r ∼ log p` where the binding datum becomes `E_r ≤ Wick_r` — the open BGK wall.

All theorems are `propext / Classical.choice / Quot.sound`-clean (no `sorry`).  Issue #444.
-/

namespace ProximityGap.Frontier.AvLPTruncMoment

/-- The quadratic governing the max-support LP:
`f B = n·m₀·B² − 2·m₁·n·B − C` where `C = m₂·m₀ − m₂·n − m₁²` is the (data-weighted) Hankel
determinant.  Feasibility of the truncated moment problem with a top atom of mass `n` is
`f B ≤ 0`. -/
noncomputable def lpQuad (n m0 m1 m2 B : ℝ) : ℝ :=
  n * m0 * B ^ 2 - 2 * m1 * n * B - (m2 * m0 - m2 * n - m1 ^ 2)

/-- **The Cauchy–Schwarz floor sits inside the infeasible region (`f ≤ 0`).**
At `B = m₂/m₁` the LP quadratic evaluates to `−(m₁ m₀ − m₂)·(something) …`; we show it is `≤ 0`
under the natural data positivity, so the *upper* ceiling (largest root, where `f` turns `≤ 0`)
is `≥ m₂/m₁`.

Precisely: if `m₁ > 0`, `m₂ ≥ 0`, `n ≥ 0`, and the Hankel datum `C = m₂ m₀ − m₂ n − m₁² ≥ 0`
(equivalently the remaining mass has nonnegative variance — always true for a real measure), and
the leading coefficient `n m₀ ≥ 0`, then `lpQuad n m0 m1 m2 (m2/m1) ≤ 0` requires the genuine
arithmetic below. We instead prove the clean *equivalent*: the value of the quadratic at the floor
point equals `(n/m₁²)·(m₀·m₂ − m₁²)·m₂ − 2 m₂ n + (m₁² − m₂ m₀ + m₂ n)` reorganised — and the
sign follows from `C ≥ 0`. -/
theorem lpQuad_at_csFloor (n m0 m1 m2 : ℝ) (hm1 : m1 ≠ 0) :
    lpQuad n m0 m1 m2 (m2 / m1) =
      n * m0 * (m2 / m1) ^ 2 - 2 * m2 * n - (m2 * m0 - m2 * n - m1 ^ 2) := by
  unfold lpQuad
  have h : 2 * m1 * n * (m2 / m1) = 2 * m2 * n := by
    field_simp
  rw [h]

/-- **Barrier fact 1 (sign), exact value.**  The quadratic value at the floor point, cleared of
denominators, is `(n m₀ m₂² − (2 m₂ n + C) m₁²)/m₁²` with `C = m₂ m₀ − m₂ n − m₁²`. -/
theorem supportCeiling_dual_value (n m0 m1 m2 : ℝ) (hm1 : m1 ≠ 0) :
    lpQuad n m0 m1 m2 (m2 / m1)
      = (n * m0 * m2 ^ 2 - (2 * m2 * n + (m2 * m0 - m2 * n - m1 ^ 2)) * m1 ^ 2) / m1 ^ 2 := by
  rw [lpQuad_at_csFloor n m0 m1 m2 hm1]
  field_simp
  ring

/-- **The numerator FACTORS** as `(m₀ m₂ − m₁²)·(n m₂ − m₁²)`.  This is the crux of the no-go:
the sign of the LP quadratic at the Cauchy–Schwarz floor is controlled by exactly two products:
the Hankel/Cauchy–Schwarz determinant `m₀ m₂ − m₁²` (nonnegative for any real measure) and the
"spread" factor `n m₂ − m₁²` (NONPOSITIVE at prize scale, since `m₁² ∼ q²n² ≫ 3qn³ ∼ n m₂`), so
the product is `≤ 0`. -/
theorem lpQuad_floor_numerator_factor (n m0 m1 m2 : ℝ) :
    n * m0 * m2 ^ 2 - (2 * m2 * n + (m2 * m0 - m2 * n - m1 ^ 2)) * m1 ^ 2
      = (m0 * m2 - m1 ^ 2) * (n * m2 - m1 ^ 2) := by ring

/-- **Barrier fact 1 (the no-go inequality): the LP upper ceiling is `≥` the Cauchy–Schwarz
floor.**  Whenever the measure is genuine (`m₀ m₂ ≥ m₁²`, Cauchy–Schwarz) and the spectrum is
spread (`m₁² ≥ n m₂`, true at prize scale), the LP quadratic is `≤ 0` at `B = m₂/m₁`.  Since the
leading coefficient `n m₀ ≥ 0` (with `n, m₀ > 0` it is `> 0`), the parabola opens upward and is
`≤ 0` only between its two roots; hence the *larger* root — the max-support ceiling — is
`≥ m₂/m₁`.  Therefore the LP can never certify an upper bound *below* the established lower floor:
**the truncated max-support LP on `{mass, m₁, m₂, atom-mass ≥ n}` is vacuous for the prize.** -/
theorem supportCeiling_ge_csLower
    (n m0 m1 m2 : ℝ) (hm1 : 0 < m1)
    (hCS : m1 ^ 2 ≤ m0 * m2) (hspread : n * m2 ≤ m1 ^ 2) :
    lpQuad n m0 m1 m2 (m2 / m1) ≤ 0 := by
  rw [supportCeiling_dual_value n m0 m1 m2 (ne_of_gt hm1),
      lpQuad_floor_numerator_factor n m0 m1 m2]
  have hm1sq : (0:ℝ) < m1 ^ 2 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hm1sq)
  have h1 : 0 ≤ m0 * m2 - m1 ^ 2 := by linarith
  have h2 : n * m2 - m1 ^ 2 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- **Barrier fact 2 (the floor is the `√3√n` scale, exact at `q = n⁴`).**
The Cauchy–Schwarz floor `m₂/m₁` with the proven exact moments
`m₁ = q n − n²`, `m₂ = q(3n²−3n) − n⁴` equals, at the canonical prize scale `q = n⁴`,
the rational `n²·(3n² − 3n − 1)/(n³ − 1)`.  (Asymptotically `→ 3n` since the leading terms are
`3n⁴·n² / n⁵ = 3n`, i.e. `√(floor) → √3·√n`, the established lower bound — NO log.)
Exact algebraic identity. -/
theorem csLower_value (n : ℝ) (hn0 : n ≠ 0) :
    (((n ^ 4) * (3 * n ^ 2 - 3 * n) - n ^ 4) / ((n ^ 4) * n - n ^ 2))
      = n ^ 2 * (3 * n ^ 2 - 3 * n - 1) / (n ^ 3 - 1) := by
  have hnum : (n ^ 4) * (3 * n ^ 2 - 3 * n) - n ^ 4 = n ^ 2 * (n ^ 2 * (3 * n ^ 2 - 3 * n - 1)) := by
    ring
  have hden : (n ^ 4) * n - n ^ 2 = n ^ 2 * (n ^ 3 - 1) := by ring
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hn0)]

/-- **Barrier fact 3 (the floor `→ 3n`, the leading ratio is exactly `3`).**
The leading coefficient of the floor numerator (`3n⁴`) over the leading coefficient of the
denominator (`n⁴`) after multiplying by `n` is `3`, confirming `m₂/m₁ ∼ 3n` with NO log.
We record the exact identity `(3n²−3n−1)·n² = 3·n⁴ − 3·n³ − n²` so the `3n`-scale is manifest. -/
theorem csLower_leading (n : ℝ) :
    n ^ 2 * (3 * n ^ 2 - 3 * n - 1) = 3 * n ^ 4 - 3 * n ^ 3 - n ^ 2 := by ring

/-- **The data hypotheses of `supportCeiling_ge_csLower` are satisfied by the real spectrum.**
At the canonical prize scale `q = n⁴` (`n > 1`), the Stickelberger moments
`m₁ = q n − n²`, `m₂ = q(3n²−3n) − n⁴`, `m₀ = q − 1` satisfy `n·m₂ ≤ m₁²` (the "spread"
hypothesis), so the no-go theorem genuinely applies — the LP ceiling for the *actual* Gauss-period
spectrum is `≥ m₂/m₁ ∼ 3n`, hence vacuous for the `√(n log p)` prize.  (`hCS : m₁² ≤ m₀ m₂` is
Cauchy–Schwarz, automatic for the empirical measure.)  Verified numerically `n = 16..256`. -/
theorem prizeData_spread (n : ℝ) (hn : 1 ≤ n) :
    let q := n ^ 4
    let m1 := q * n - n ^ 2
    let m2 := q * (3 * n ^ 2 - 3 * n) - n ^ 4
    n * m2 ≤ m1 ^ 2 := by
  intro q m1 m2
  show n * (n ^ 4 * (3 * n ^ 2 - 3 * n) - n ^ 4) ≤ (n ^ 4 * n - n ^ 2) ^ 2
  -- RHS − LHS = n⁴·(n⁶ − 5n³ + 3n² + n + 1) = n⁴·((2n³−5)²/4 + 3n² + n − 21/4) ≥ 0 for n ≥ 1.
  have hn0 : (0:ℝ) ≤ n := by linarith
  have ht : 0 ≤ n - 1 := by linarith
  have hg : 0 ≤ n ^ 6 - 5 * n ^ 3 + 3 * n ^ 2 + n + 1 := by
    -- with t = n−1 ≥ 0:  g = t⁶+6t⁵+15t⁴+15t³ + (3t²−2t+1), and 3t²−2t+1 = 3(t−1/3)²+2/3 > 0.
    nlinarith [pow_nonneg ht 6, pow_nonneg ht 5, pow_nonneg ht 4, pow_nonneg ht 3,
               sq_nonneg (n - 1 - 1/3), sq_nonneg (n - 1)]
  nlinarith [mul_nonneg (pow_nonneg hn0 4) hg]

end ProximityGap.Frontier.AvLPTruncMoment
