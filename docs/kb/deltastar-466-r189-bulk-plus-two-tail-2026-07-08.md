# δ* #466 — bulk-plus-two tail route to quarter MGF (2026-07-08)

## Hypothesis

R188 named the active residual:

```text
DyadicQuarterMGFBound s t
```

equivalently

```text
(1/M) Σ_i exp(t_i / 4) ≤ 2.
```

R189 tests whether this can be proved by a sharper two-regime survival law:

```text
N(T) ≤ (3/5) M exp(-T/2) + 2.
```

Interpretation:

- `(3/5) M exp(-T/2)` is the Gaussian-like bulk.
- `+ 2` absorbs the rare coherent spike cosets that defeated the pure
  `exp(-T/2)` envelope in R63-style adversarial primes.

## Probe

File: `scripts/probes/probe_r189_bulk_plus_spikes_tail.py`.

Default certificate:

```text
C_bulk = 0.60
spike_budget = 2
grid step = 0.5
```

The probe also computes the half-grid layer-cake budget for `exp(X/4)` using
the envelope above.

## Result

Bounded exact run:

```text
bulk-plus-spikes envelope: N(T) <= 0.6 M exp(-T/2) + 2.0
grid step=0.5 tested_cases=90 violations=0

worst_budget=1.819292 n=16 p=257
worst_mgf1/4=1.523404
max_positive_excess=0.000000
```

The slightly larger constants also survive:

```text
C_bulk = 0.62, K = 2: violations=0, worst_budget=1.830405
C_bulk = 0.65, K = 2: violations=0, worst_budget=1.847075
```

Earlier failed variants identify the shape:

```text
C_bulk = 0.55, K = 1: spike-threshold failures
C_bulk = 0.55, K = 2: only low-threshold bulk failures
C_bulk = 0.60, K = 2: no failures
```

## Verdict

This is the strongest current proof target for `DyadicQuarterMGFBound`:

```text
For every half-grid T >= 1,
  #{i : T <= t_i} <= (3/5) M exp(-T/2) + 2.
```

Together with the explicit half-grid layer-cake budget, this implies the
quarter-MGF residual with slack below `2`, then R188/R185/R168 feed the prize
pipeline.

The remaining analytic content is now narrower than a raw MGF bound: prove a
Gaussian bulk tail plus a two-coset coherent-spike allowance for dyadic
Gauss-period spectra.
