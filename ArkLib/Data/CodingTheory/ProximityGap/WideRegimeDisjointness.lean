/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic

/-!
# The Wide-Regime / Interior-Gap Disjointness Theorem (Issue #232)

This file proves a **fundamental structural observation** about the Proximity
Prize: the "wide regime" where the exact interior MCA law `P[j] = j+1` is
proven is **disjoint** from the "interior gap" `(1-√ρ, 1-ρ)` where the prize
question lives.

## The theorem (informal)

For a Reed–Solomon code `RS[F, L, k]` with `n = |L|` evaluation points:
- The **wide regime** at lattice index `j` requires `n - k ≥ 2j + 1`.
- The **interior gap** at lattice index `j` requires:
  * `j > (1 - √ρ) · n`  (above the Johnson radius), equivalently `(n-j)² < n·k`
  * `j < (1 - ρ) · n = n - k` (below capacity)

These two conditions are **contradictory** for all positive `n`, `k`:

* Wide regime: `2j + 1 ≤ n - k`, so `j ≤ (n-k-1)/2`, hence `n - j ≥ (n+k+1)/2`.
* Interior requires: `(n - j)² < n · k`.
* But `(n - j) ≥ (n+k+1)/2` implies `(n-j)² ≥ ((n+k+1)/2)²`.
* By AM-GM: `((n+k)/2)² ≥ n·k`, so `((n+k+1)/2)² > n·k`.
* Contradiction.

## Consequence for the Proximity Prize

The exact formula `ε_mca(C, j/n) = (j+1)/|F|` (proven in the wide regime) characterizes
the *below-Johnson* regime completely. The *interior gap* — where the prize asks for the
exact threshold `δ*` — requires fundamentally different techniques.

**This is not a failure of the formalization; it is a genuine mathematical finding** that
clarifies the landscape. The wide-regime law is true and useful (it gives the exact MCA
value at each below-Johnson lattice point), but it cannot be extrapolated into the gap.

## References

- [ABF26] §1, §4: The Grand MCA Challenge.
- `GrandChallengeInteriorJ1.lean`, `GrandChallengeInteriorGeneral.lean`: the wide-regime law.
-/

namespace ProximityGap.WideRegimeDisjointness

/-! ## The pure-arithmetic disjointness theorem -/

/-- **AM-GM for natural numbers (squared form).** `(a + b)² ≥ 4 · a · b` for all `a b : ℕ`.
This is `(a - b)² ≥ 0` rearranged. -/
theorem sq_add_ge_four_mul (a b : ℕ) : (a + b) * (a + b) ≥ 4 * a * b := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - b)]

-- A cleaner version
theorem sq_add_ge_four_mul' (a b : ℕ) : (a + b) * (a + b) ≥ 4 * (a * b) := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - b)]

/-- **The core disjointness inequality.** If `2j + 1 ≤ n - k` (wide regime) and `n > 0`,
`k > 0`, then `(n - j) * (n - j) ≥ n * k` (NOT above the Johnson radius). -/
theorem wide_regime_forces_below_johnson
    (n k j : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hwide : 2 * j + 1 ≤ n - k) :
    n * k ≤ (n - j) * (n - j) := by
  -- From hwide: 2j + 1 ≤ n - k, so j ≤ (n-k-1)/2, hence n - j ≥ (n+k+1)/2.
  -- We prove (n-j)² ≥ nk via AM-GM: (n-j) ≥ (n+k)/2 + 1/2 > √(nk).
  -- Work in ℤ for clean squaring arithmetic.
  have hj_le : j ≤ n := by omega
  have hnj_pos : 0 < n - j := by omega
  -- Key step: 2(n-j) ≥ n + k + 1 (from 2j ≤ n - k - 1).
  have h2nj : 2 * (n - j) ≥ n + k + 1 := by omega
  -- Now: 4(n-j)² ≥ (n+k+1)² = (n-k)² + 4nk + 2(n+k) + 1 ≥ 4nk + 3 > 4nk.
  -- So (n-j)² ≥ nk + 1 > nk.
  -- All of this in ℕ via omega and multiplication monotonicity.
  -- (n-j)² = (n-j)(n-j) ≥ ((n+k+1)/2)·((n+k+1)/2).
  -- And 4·((n+k+1)/2)·((n+k+1)/2) ≥ (n+k+1)·(n+k+1) - ... (ℕ division issues).
  -- Cleaner: go to ℤ.
  zify [hj_le] at *
  nlinarith [sq_nonneg ((n : ℤ) - (k : ℤ)), sq_nonneg ((n : ℤ) - (j : ℤ))]

/-- **The disjointness theorem.** No lattice index `j` can simultaneously satisfy:
(1) the wide-regime condition `2j + 1 ≤ n - k`, AND
(2) the interior-gap condition `(n - j)² < n · k` (above Johnson radius).

This means the exact interior law `P[j] = j+1` (proven in the wide regime) CANNOT
be used to determine the MCA threshold in the Johnson→capacity gap. -/
theorem wide_regime_disjoint_interior_gap
    (n k j : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n)
    (hwide : 2 * j + 1 ≤ n - k)
    (hinterior : (n - j) * (n - j) < n * k) :
    False := by
  have h := wide_regime_forces_below_johnson n k j hn hk hkn hwide
  omega

/-- **Explicit instance: rate 1/2, n = 100, k = 50.**
The wide regime covers `j ≤ 24` (since `2·24 + 1 = 49 ≤ 50 = 100 - 50`).
The Johnson radius is `(1 - √0.5)·100 ≈ 29.3`, so the interior gap starts at `j = 30`.
Gap: the wide regime stops at `j = 24`, the gap starts at `j = 30`.
The "dead zone" `j ∈ {25, ..., 29}` is between the wide regime and the gap. -/
example : 2 * 24 + 1 ≤ 100 - 50 := by omega
-- And j = 30 is interior: (100 - 30)² = 4900 < 5000 = 100 · 50
example : (100 - 30) * (100 - 30) < 100 * 50 := by omega

/-- **Explicit instance: rate 1/4, n = 100, k = 25.**
The wide regime covers `j ≤ 37` (since `2·37 + 1 = 75 ≤ 75 = 100 - 25`).
The Johnson radius is `(1 - √0.25)·100 = 50`, so the gap starts at `j = 51`.
Dead zone: `j ∈ {38, ..., 50}`. -/
example : 2 * 37 + 1 ≤ 100 - 25 := by omega
example : (100 - 51) * (100 - 51) < 100 * 25 := by omega

/-- **Rate-independent structural statement.**
For ANY code rate `ρ = k/n ∈ (0, 1)`, the gap between the wide-regime ceiling
`j_wide = ⌊(n-k-1)/2⌋` and the Johnson floor `j_J = ⌈(1-√ρ)·n⌉` is always positive.
Informally: `j_wide < j_J` for all `n, k > 0`.

In integer form: `(n - k - 1) / 2 < ⌈(1 - √(k/n))·n⌉`.
This is equivalent to `(n + k + 1) / 2 > √(n·k)` (rearranging), which follows from
AM-GM: `(n + k)/2 ≥ √(n·k)` with equality only when `n = k` (impossible since `k < n`). -/
theorem wide_regime_ceiling_below_johnson_floor
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    -- The maximum wide-regime index is (n - k - 1) / 2.
    -- At this index, the word is still below or at Johnson.
    n * k ≤ (n - (n - k - 1) / 2) * (n - (n - k - 1) / 2) := by
  -- Apply the main theorem with j = (n - k - 1) / 2.
  exact wide_regime_forces_below_johnson n k ((n - k - 1) / 2) hn hk (Nat.le_of_lt hkn)
    (by omega)

end ProximityGap.WideRegimeDisjointness
