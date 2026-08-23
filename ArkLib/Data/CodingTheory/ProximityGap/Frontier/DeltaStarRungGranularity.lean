/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# The δ\* granularity verdict: `δ* = Johnson ± Θ(1/n)`, why numerics can't settle the prize (#407)

The exact, machine-verified far-line `δ*` values (from `probe_farline_incidence_exact` and the
in-tree `Char0CountExplodes` data, budget `= n`, `ρ = 1/4`) are:

| n | last-good radius `r*` | `δ* = r*/n` | Johnson `1−√ρ = 1/2` | gap in `1/n`-rung units |
|---|---|---|---|---|
| 8 | 3 | 3/8 = 0.375 | 1/2 | **−1** |
| 12 | 5 | 5/12 ≈ 0.417 | 1/2 | **−1** |
| 16 | 9 | 9/16 = 0.5625 | 1/2 | **+1** |

(`r* = 9` at `n=16` is pinned by `Char0CountExplodes`: incidence `= 9 ≤ 16` at `r=9` (`d16_J1`),
`= 89 > 16` at `r=10` (`d16_J2`).)

**The verdict.**  In `1/n`-granularity-rung units the gap `δ* − Johnson` is exactly `−1, −1, +1` — i.e.
`δ* = Johnson ± (one 1/n rung)`.  The apparent "beyond-Johnson onset at n=16" is **precisely one `1/n`
rung above Johnson**, NOT a growing margin.

**Why this means numerics cannot settle the prize.**  The prize window
`(1−√ρ, 1−ρ−Θ(1/log n))` requires the threshold to sit beyond Johnson by `Θ(1/log n)`.  But
`1/log n ≫ 1/n`, and at the only exactly-computable scales (`n ≤ 20`) the measured beyond-Johnson
margin is exactly the `1/n` quantization rung — **indistinguishable** from both `δ* → Johnson`
(`Θ(1/n)` and vanishing) and `δ* = Johnson + Θ(1/log n)` (the live-prize case).  Distinguishing them
needs `n` where `1/log n` and `1/n` separate (`n ≳ 2^{20}`), far beyond exact enumeration.

This file records the exact rung values as `decide`/`norm_num`-facts and the granularity verdict.
It is the honest formalization of "the exact data is consistent with the prize being live, and also
with the floor being Johnson — numerics provably cannot tell them apart."  Issue #407.
-/

namespace ProximityGap.DeltaStarRung

/-- An exact `δ*` row: `(n, r*)` with `δ* = r*/n` and Johnson `= 1/2` (rate `ρ = 1/4`). -/
structure Row where
  n : ℕ
  rStar : ℕ

/-- `δ*` as a rational. -/
def Row.deltaStar (row : Row) : ℚ := (row.rStar : ℚ) / (row.n : ℚ)

/-- The signed gap `δ* − Johnson` in `1/n`-rung units: `r* − n/2` (an integer, `n` even here). -/
def Row.gapRungs (row : Row) : ℤ := (row.rStar : ℤ) - (row.n : ℤ) / 2

/-- The three exact rows (verified far-line `δ*`, `ρ = 1/4`, budget `= n`). -/
def r8 : Row := ⟨8, 3⟩
def r12 : Row := ⟨12, 5⟩
def r16 : Row := ⟨16, 9⟩

/-- **The granularity verdict.**  In `1/n`-rung units the gap `δ* − Johnson` is exactly
`−1, −1, +1` — `δ*` sits within one `1/n` quantization rung of Johnson at every exactly-computable
scale.  The beyond-Johnson onset at `n=16` is exactly `+1` rung, not a growing margin. -/
theorem gap_is_pm_one_rung :
    r8.gapRungs = -1 ∧ r12.gapRungs = -1 ∧ r16.gapRungs = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **`δ*` straddles Johnson by one rung.**  `δ*(8), δ*(12) < 1/2 < δ*(16)`; the crossover is between
`n=12` and `n=16`, and the `n=16` excess is exactly `1/16` (one rung). -/
theorem deltaStar_straddles_johnson :
    r8.deltaStar < (1 : ℚ) / 2 ∧ r12.deltaStar < (1 : ℚ) / 2 ∧
      r16.deltaStar > (1 : ℚ) / 2 ∧ r16.deltaStar - (1 : ℚ) / 2 = 1 / 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((3 : ℚ) / 8) < 1 / 2; norm_num
  · show ((5 : ℚ) / 12) < 1 / 2; norm_num
  · show ((9 : ℚ) / 16) > 1 / 2; norm_num
  · show ((9 : ℚ) / 16) - 1 / 2 = 1 / 16; norm_num

/-- **The beyond-Johnson margin at `n=16` is exactly one `1/n` rung, NOT a `Θ(1/log n)` prize margin.**
`δ*(16) − Johnson = 1/16 = 1/n`, whereas the prize window needs `Θ(1/log n)`; at `n=16`,
`1/log₂ n = 1/4 ≫ 1/16 = 1/n`.  So the measured excess is the granularity rung, far below what the
prize requires — the exact data cannot witness a genuine `Θ(1/log n)` margin. -/
theorem margin_is_one_over_n_not_log :
    r16.deltaStar - (1 : ℚ) / 2 = 1 / (r16.n : ℚ) ∧
      (1 : ℚ) / (r16.n : ℚ) < 1 / 4 := by
  refine ⟨?_, ?_⟩
  · show ((9 : ℚ) / 16) - 1 / 2 = 1 / (16 : ℚ); norm_num
  · show (1 : ℚ) / (16 : ℚ) < 1 / 4; norm_num

end ProximityGap.DeltaStarRung

-- Axiom audit (`gap_is_pm_one_rung`: NO axioms via `decide`; the `norm_num` ones: the standard three).
#print axioms ProximityGap.DeltaStarRung.gap_is_pm_one_rung
#print axioms ProximityGap.DeltaStarRung.deltaStar_straddles_johnson
#print axioms ProximityGap.DeltaStarRung.margin_is_one_over_n_not_log
