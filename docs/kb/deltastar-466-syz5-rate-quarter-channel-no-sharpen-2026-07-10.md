# SYZ5: the degenerate channel does NOT sharpen the rate-1/4 ceiling — integer-D floor is 1/2 > 43/96 (2026-07-10)

Status: axiom-clean LANDED as a **barrier** (not a pin). The SYZ4 kb note predicted a rate-1/4
analogue at the channel infimum `(1−ρ)/(2−ρ) = 3/7 ≈ 0.4286`, below the current unconditional
rate-1/4 ceiling `43/96 + 1/(3·2^30) ≈ 0.44792`. **That prediction is unattainable.**

## Prior-art / current ceiling

Current unconditional in-tree rate-1/4 production ceiling (to beat):
`_P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_le_common_delta` (unconditional, no
`_of_structured` hypothesis):

  `mcaDeltaStar (evalCode g (2^30) (2^28 − 1)) epsStar ≤ deltaCommon = 480946859/2^30 = 43/96 + 1/(3·2^30) ≈ 0.44792`.

(The `_of_structured` exact pin at the same `43/96 + 1/(3·2^30)` is conditional; the `≤` version is
unconditional.) No SYZ5 / rate-1/4 SYZ ceiling had landed concurrently (grep of Frontier/kb/DISPROOF_LOG).

## Why 3/7 is unattainable and 1/2 is the integer floor

The infimum `(1−ρ)/(2−ρ)` is a **continuous-`D`** optimum, realized only at the non-integer subset
count `D = (1−ρ)/((1−ρ)²/(2−ρ)) = 7/3`. With a whole number of degenerate subsets the achievable
floor is `min_{D∈ℕ} max(1/D, (1−ρ)(1−1/D))`. At `ρ = 1/4`:

  D=2 → max(1/2, 3/8) = 1/2;  D=3 → max(1/3, 1/2) = 1/2;  D=4 → 9/16;  D≥4 grows.

So the best integer rung is **1/2**, and `1/2 > 43/96` — no sharpening.

Structural reason (`c_j = n − t_j`, agreement `t_j = core + a_j`, degree cap `4·core ≤ n`, regions
disjoint `core + Σa_j ≤ n`): for `D = 3`, `Σ c_j = 3n − 3·core − Σa_j ≥ 3n − 3(n/4) − (n−core) ≥ 3n/2`,
so `max c_j ≥ avg ≥ n/2` — with **no** budget hypothesis. For `D ≤ 2` the `ε*`-budget `Σc_j > n`
forces `max c_j > n/2`. Concrete 64-block/core-15 D=3 rung would give `33/64 ≈ 0.516`; finer grading
→ `1/2⁺`. All above `43/96` and above the `3/8` good-floor — consistent, no progress.

## Theorems (`Frontier/_SYZ5RateQuarterChannelCeiling.lean`, axiom-clean, only propext)

- `rateQuarter_channel_D3_radius_ge_half`: degree cap + disjointness ⇒ some complement `≥ n/2` (D=3, budget-free).
- `rateQuarter_channel_D2_radius_ge_half`: budget ⇒ some complement `≥ n/2` (D=2).
- `total_complement_lower_bound`: general `D`, `Σ_j c_j ≥ (D−1)(n−core)` (the averaging driver).
- `channel_does_not_sharpen_rateQuarter_ceiling`: `480946859/2^30 < 1/2` and `3/7 < 1/2`.

## Honest gaps / status

- This is a NO-GO for the degenerate-subset channel at rate 1/4, not a new ceiling. The current
  `43/96 + 1/(3·2^30)` ceiling stands; `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` bracket unchanged.
- Full production consumer (`mcaDeltaStar ≤ radius`) deliberately NOT wired: it would only reprove
  a ceiling `≥ 1/2`, strictly weaker than the extant one.
- CORE (exact pin) OPEN. Beating `43/96` at rate 1/4 needs a genuinely different construction than
  the SYZ degenerate channel (or a fractional-D emulation with an honest count).

Issue #466 / #507. SYZ arc: SYZ4 (rate-1/2 ceiling, LANDED) → SYZ5 (rate-1/4 no-go, this).
