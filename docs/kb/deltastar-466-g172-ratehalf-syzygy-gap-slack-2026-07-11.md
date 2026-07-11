# δ* #466 — G172: the rate-1/2 syzygy degree gap with slack (2026-07-11)

## One-line

At the prize rate exactly (`2k = n`), SYZ38's `SylvesterInjective` residual is **degree-forced and
field-independent**; SYZ39's genuine bad primes are a **rate > 1/2** phenomenon. The mechanism is a
combinatorial-slack + bounded-μ-basis-imbalance argument, not a resultant nonvanishing.

## Context

- SYZ38 reduced the entire rate-1/2 proximity residual to `SylvesterInjective W_AB W_AC W_BC b_AC b_BC`
  (generalized Sylvester map injective on the in-budget cofactor window) and framed the 3-support case
  as "genuinely resultant-type (field-dependent)".
- SYZ39 gave a bad-prime law: the gcd of Sylvester maximal minors has a rational norm whose prime
  factors are the bad primes (e.g. `n=13`, rate `7/13`: `53,79,103,131,157,181`).
- Fresh referee (Fable, 11:52 UTC): at rate exactly 1/2 injectivity is a pure degree count
  `b_AC + b_BC < deg W_AB`, no resultant.

**All three are partly right; none of the stated reasons is the correct one.** G172 pins it.

## The exact mechanism

Reduced degrees `a = m_AB − t`, `b = m_AC − t`, `c = m_BC − t`; budget `= k − 1 − t`.

1. **Degree-sum law** (probe, field-independent): the syzygy module of the pairwise-coprime triple
   mapping onto `K[X]` is rank-2 free with `d1 + d2 = a + b + c`, so `d1 ≤ ⌊(a+b+c)/2⌋`.
2. **μ-basis imbalance is bounded**: `ι = ⌊(a+b+c)/2⌋ − d1 ≤ 1` over 5542 adversarial triples
   (`n=16..56`, 4 primes, 4 root families), and `ι = 1` occurs only when `a+b+c` is even (gap 2).
3. **Combinatorial slack** (theorem, pure ℕ): interior band `3s ≥ 2n+1` + inclusion-exclusion ⟹
   `m_AB + m_AC + m_BC ≥ n + t + 1` ⟹ `a + b + c ≥ 2(k − t) + 1` ⟹ balanced min degree
   `⌊(a+b+c)/2⌋ ≥ k − t = budget + 1`.
4. **Slack absorbs imbalance**: even at max imbalance the true minimal syzygy degree
   `d1 ≥ budget + 1`, so the in-budget kernel is `{0}` — `SylvesterInjective` holds. MIN margin
   `d1 − budget = 1` across all 5542 triples; zero in-budget syzygies; zero field-flips.

## Why NOT Fable's `b_AC + b_BC < deg W_AB`

That inequality *does* hold at rate 1/2 (margin ≥ 3 in the probe), but it does not force injectivity:
the products `W_AC · r_AC` have degree `~ deg W_AC + b_AC`, far exceeding `deg W_AB`, so the reduction
mod `W_AB` is genuinely needed. The correct forcing is the *minimal syzygy degree* exceeding the
budget window, which is a μ-basis-degree statement (Shaw's object), tamed by the interior slack.

## No-go (the residual's exact location)

Any rate-1/2 injectivity failure requires μ-basis imbalance `≥ 2`
(`failure_forces_imbalance_ge_two`); at gap 1 (odd `a+b+c`) it needs imbalance `≥ 1` where the probe
shows imbalance `0` (`gap_one_failure_forces_imbalance_ge_one`). The imbalance-`≥2` regime is exactly
SYZ39's bad-prime resultant regime, which all evidence confines to rate `> 1/2` (`2k > n`) and which
never fires below the prize characteristic.

## Landed theorems (`_G172RateHalfSyzygyGapSlack.lean`, axiom-clean)

`interior_overlap_sum_lower`, `reduced_degree_sum_lower`, `balanced_syzygy_gap`,
`balanced_min_degree_gt_budget`, `degree_gap_survives_imbalance`, `eq_zero_of_dvd_of_natDegree_lt`,
`sylvester_injective_of_diff_natDegree_lt`, `failure_forces_imbalance_ge_two`,
`gap_one_failure_forces_imbalance_ge_one`.

## Honest scope

The two μ-basis facts (degree-sum law, `ι ≤ 1`) are the genuine resultant content and are **not**
proved here (they match SYZ38/SYZ39's honest framing). G172 proves the pure-ℕ slack skeleton, the
elementary degree-count injectivity criterion, and the no-go. It discharges only SYZ33 lemma 2 at
rate 1/2; the δ* production wire still needs lemma-1 supports, the general-`D` peel, SYZ22
realizability, and the `MCAThresholdLedger` BGK/incidence lower bound. **CORE OPEN / ON-BGK.**

## Reproduce

```
python3 scripts/probes/probe_466_g172_sylvester_ratehalf_rank.py
python3 scripts/probes/probe_466_g172_margin_robustness.py
```
