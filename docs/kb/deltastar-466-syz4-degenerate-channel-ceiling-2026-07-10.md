# SYZ4: NEW unconditional production ceiling — δ*(rate 1/2) ≤ 369098751/2^30 = 11/32 − 2^-30 ≈ 0.34375 (2026-07-10)

Status: axiom-clean LANDED; sharpens the in-tree production rate-1/2 ceiling from 31/64 ≈ 0.484.
The channel's infimum is (1−ρ)/(2−ρ) = 1/3 at rate 1/2; the landed rung is 11/32 − 2^-30 due to
the 64-block radius lattice. Johnson (1−√ρ ≈ 0.2929) remains below — no contradiction.

## Mechanism

The SYZ degenerate-subset channel (SYZ1 probe → SYZ2 pencil → SYZ3 witness), run at an OPTIMIZED
agreement threshold rather than the 31/64 predecessor: with m = t−k and D ≈ (n−k)/m degenerate
subsets, the explicit glue stack carries D·(n−t) distinct mcaEvent-bad scalars; this beats the
ε*-budget (ε*·P ≈ 2^30) for every radius above (1−ρ)/(2−ρ). Landed rung: t = 42·2^24, D = 3,
yield 3·22·2^24 = 1107296256 > 2^30, hence epsMCA > ε* at δ = predecessorRadius(2^30, 22·2^24),
hence mcaDeltaStar ≤ that radius < 11/32.

## Theorems (`Frontier/_SYZ4DegenerateChannelCeiling.lean`, axiom-clean 4/4)

- `badScalar_count_over_budget`
- `firstPrime_rateHalf_mcaDeltaStar_le_syz4` / `..._le_exact`: mcaDeltaStar ≤ 369098751/2^30
- `syz4_radius_lt_elevenThirtyTwo`

## New production bracket (rate 1/2, first certified field)

178956971/2^30 ≈ 0.16667  ≤  δ*  ≤  369098751/2^30 ≈ 0.34375
(previously ceiling 31/64 ≈ 0.484). Curious numerology: the floor numerator 178956971 equals the
channel's optimal m (n−k = 3m exactly); the channel infimum radius is 178956971/2^29 = 2×floor.

## Honest gaps / next steps

1. Radius lattice: a 2^13-block grading would push the rung toward 1/3⁺ (same channel, heavier
   decide layer). The infimum (1−ρ)/(2−ρ) is the channel's limit — closing the remaining
   [Johnson ≈ 0.2929, 1/3] gap needs a genuinely different construction or a matching floor.
2. Second certified field (budget 2^31): current stack does not beat it; needs finer variant.
3. Rate-1/4 analogue predicts (1−ρ)/(2−ρ) = 3/7 ≈ 0.4286 < current 43/96 ≈ 0.4479 rate-quarter
   ceiling — worth its own instantiation.
4. Floor and CORE (exact pin) untouched/OPEN.

Prior-art check: grep of kb/Frontier/DISPROOF_LOG for the bound and its forms found nothing;
the 31/64 route was quotient/packing-based and the SYZ arc had only been used to refute its
hypothesis, not to build ceilings. Issue #466 / #507. SYZ arc: SYZ1 (4351c0d83), SYZ2
(e14d04bf3), SYZ3 (efb83bef9), SYZ4 (this).
