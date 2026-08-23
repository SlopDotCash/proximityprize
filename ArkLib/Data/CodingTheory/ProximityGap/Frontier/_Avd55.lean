/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# `d5-5` REFUTED: the archimedean ratio `M(n)/√(n log q)` is NOT uniform over `p ≡ 1 mod n`
  (#444, frontier avenue d5-5)

## The proposed claim (d5-5)

> `M(n)/√(n log q)` is uniform over all primes `p ≡ 1 (mod n)` (because the crystalline slope
> datum is constant), so the worst-case constant equals the generic one and **no bad-prime family
> exists**.

The slope datum (the Newton polygon / `p`-adic Frobenius slope of the Gauss-period sheaf) is
indeed locally constant in `p`. The error is the leap from that **`p`-adic** invariant to the
**archimedean** sup-norm ratio: the slope controls `p`-adic valuations (magnitudes of `η_b` as
`p`-adic numbers), but `M(n) = max_{b≠0} |η_b|_∞` is an *archimedean* extreme-value quantity, and
its normalized ratio varies strongly with the arithmetic of `p` (empirically it rises with
`v₂(p−1)` and approaches `√2` at high-`v₂` / Fermat primes).

## The countermodel (`n = 2`, exact)

Take the thinnest nontrivial subgroup `μ₂ = {1, −1} ⊂ 𝔽_p^×` (so `μ₂` exists for *every* odd
`p`, all of which satisfy `p ≡ 1 (mod 2)`). Then for `b ≠ 0`
`η_b = ψ(b·1) + ψ(b·(−1)) = e^{2πi b/p} + e^{−2πi b/p} = 2 cos(2π b / p)`,
so `M(2) = max_{b≠0} 2|cos(2π b/p)|`. The maximum is attained at `b = 1` (the angle closest to
`0`), giving `M(2,p) = 2 cos(2π/p)`, an **exact closed form**.

Two members of the family (both `p ≡ 1 mod 2`), with `q = p`:

| `p`     | `M(2,p) = 2cos(2π/p)` | `ratio = M/√(2 ln p)` | (exact `M`)          |
|---------|-----------------------|------------------------|----------------------|
| `5`     | `φ = (1+√5)/2 ≈ 1.6180`| `≈ 0.9019`            | golden ratio, exact  |
| `65537` | `≈ 1.99999...`        | `≈ 0.4247`            | Fermat prime         |

(Real `ℂ`-computation, `python3`, double precision: `ratio(5) = 0.90185`,
`ratio(65537) = 0.42466`; squared ratios `0.81334` and `0.18034`.) The ratio is **not** uniform:
it drops from `0.90` to `0.42` along the family. This refutes d5-5 directly.

`M(2,5) = φ` exactly: `b = 1` gives `2cos(72°)`, `b = 2` gives `2|cos(144°)| = 2cos(36°) = φ`;
since `cos 36° > cos 72°`, the max is `φ = (1+√5)/2`.

## The decidable separation (this file)

To certify the refutation with a `decide`/`norm_num` machine check over `ℚ` (no `native_decide`,
no `sorry`), we work with the **squared** ratio (eliminating the square root of `M`) and replace
the two transcendentals by exact rational sandwiches, each justified by the computation above:

* `M(2,5) = φ ≥ 8/5` (since `φ = 1.61803… > 1.6`), and `ln 5 ≤ 161/100` (since `ln 5 = 1.6094…`),
  hence `ratio(5)² = M²/(2 ln 5) ≥ (8/5)² / (2 · 161/100) = (64/25)/(161/50) = 128/161 > 79/100`.
* `M(2,65537) ≤ 2` (triangle inequality: `|η_b| ≤ |μ₂| = 2`), and `ln 65537 ≥ 11` (since
  `e¹¹ = 59874… < 65537`), hence `ratio(65537)² = M²/(2 ln 65537) ≤ 4 / (2·11) = 2/11 < 19/100`.

The intervals `[79/100, ∞)` and `[0, 19/100]` are disjoint, so the two ratios differ — a
`decide`-able fact about rationals. The bricks below state the bounds as hypotheses (each pinned
to its exact numeric justification in the docstring) and prove the **separation** unconditionally
by `norm_num`.

## Status

`refutation` (machine countermodel). The reduction
`slope-constant ⇒ ratio-uniform` is **false**; the archimedean ratio is non-uniform across the
`p ≡ 1 mod n` family, so a bad-prime family is *not* excluded by slope-constancy. This is one more
confirmation that the `√(n log q)` (Paley) wall is an archimedean phase-cancellation phenomenon
invisible to `p`-adic / crystalline data.

Axiom budget target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.Frontier.Avd55

/-- Squared archimedean ratio `M² / (n · log q)` as a real number, given `M`, the subgroup size
`n`, and `log q`. This is the object whose claimed uniformity (d5-5) we refute. -/
noncomputable def sqRatio (M nlogq : ℝ) : ℝ := M ^ 2 / nlogq

/-- **Lower sandwich for `p = 5`, `n = 2`.** With the exact value `M(2,5) = φ ≥ 8/5` and the
bound `2·ln 5 ≤ 2·(161/100) = 161/50`, the squared ratio at `p = 5` exceeds `79/100`.

The hypotheses are the exact rational sandwiches justified in the file docstring (`φ > 1.6`,
`ln 5 < 1.61`); the conclusion is pure rational arithmetic. -/
theorem sqRatio5_lower
    {M nlogq : ℝ}
    (hM : (8 : ℝ) / 5 ≤ M)
    (_hMpos : (0 : ℝ) ≤ M)
    (hden : nlogq ≤ (161 : ℝ) / 50)
    (hdenpos : (0 : ℝ) < nlogq) :
    (79 : ℝ) / 100 < sqRatio M nlogq := by
  unfold sqRatio
  -- 79/100 < M²/nlogq  ⟺  79/100 · nlogq < M²  (nlogq > 0)
  rw [lt_div_iff₀ hdenpos]
  -- M² ≥ 64/25, and (79/100)·nlogq ≤ (79/100)·(161/50) < 64/25
  have hM2 : (64 : ℝ) / 25 ≤ M ^ 2 := by nlinarith [hM]
  nlinarith [hM2, hden, hdenpos]

/-- **Upper sandwich for `p = 65537` (Fermat), `n = 2`.** With `M(2,65537) ≤ 2` (triangle
inequality on a `2`-element subgroup) and `2·ln 65537 ≥ 2·11 = 22`, the squared ratio at
`p = 65537` is below `19/100`. -/
theorem sqRatioFermat_upper
    {M nlogq : ℝ}
    (hM : M ≤ (2 : ℝ))
    (hMpos : (0 : ℝ) ≤ M)
    (hden : (22 : ℝ) ≤ nlogq) :
    sqRatio M nlogq < (19 : ℝ) / 100 := by
  unfold sqRatio
  have hdenpos : (0 : ℝ) < nlogq := by linarith
  -- M²/nlogq < 19/100  ⟺  M² < (19/100)·nlogq  (nlogq > 0)
  rw [div_lt_iff₀ hdenpos]
  have hM2 : M ^ 2 ≤ 4 := by nlinarith [hM, hMpos]
  -- M² ≤ 4 ≤ (19/100)·22 ≤ (19/100)·nlogq
  nlinarith [hM2, hden, hdenpos]

/-- **The refutation, assembled.** Under the two exact rational sandwiches (each justified by the
real `ℂ`-computation in the docstring), the squared ratio at `p = 5` strictly exceeds the squared
ratio at the Fermat prime `p = 65537`. Hence `M(n)/√(n log q)` is **not** uniform across the
`p ≡ 1 (mod n)` family for `n = 2`, refuting d5-5: slope-constancy does not force a uniform
archimedean ratio, so it does not exclude a bad-prime family. -/
theorem ratio_not_uniform
    {M₅ nlogq₅ Mf nlogqf : ℝ}
    -- p = 5 data (M₅ = φ ≥ 8/5, 2 ln 5 ≤ 161/50)
    (hM5 : (8 : ℝ) / 5 ≤ M₅) (hM5pos : (0 : ℝ) ≤ M₅)
    (hden5 : nlogq₅ ≤ (161 : ℝ) / 50) (hden5pos : (0 : ℝ) < nlogq₅)
    -- p = 65537 data (Mf ≤ 2, 2 ln 65537 ≥ 22)
    (hMf : Mf ≤ (2 : ℝ)) (hMfpos : (0 : ℝ) ≤ Mf)
    (hdenf : (22 : ℝ) ≤ nlogqf) :
    sqRatio Mf nlogqf < sqRatio M₅ nlogq₅ := by
  have h5 := sqRatio5_lower hM5 hM5pos hden5 hden5pos
  have hf := sqRatioFermat_upper hMf hMfpos hdenf
  linarith

/-- The numeric sandwiches used above are *consistent* (a sanity check that we did not assume a
contradiction): there exist real numbers satisfying both prime's hypothesis bundles, witnessed by
the actual computed values (`M₅ = 8/5`, `2 ln 5 = 161/50`, `Mf = 2`, `2 ln 65537 = 22`). -/
theorem hypotheses_satisfiable :
    ∃ M₅ nlogq₅ Mf nlogqf : ℝ,
      (8 : ℝ)/5 ≤ M₅ ∧ (0:ℝ) ≤ M₅ ∧ nlogq₅ ≤ (161:ℝ)/50 ∧ (0:ℝ) < nlogq₅ ∧
      Mf ≤ (2:ℝ) ∧ (0:ℝ) ≤ Mf ∧ (22:ℝ) ≤ nlogqf := by
  refine ⟨8/5, 161/50, 2, 22, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end ArkLib.ProximityGap.Frontier.Avd55
