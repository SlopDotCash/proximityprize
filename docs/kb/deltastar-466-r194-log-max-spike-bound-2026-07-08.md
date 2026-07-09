# δ* #466 — logarithmic max bound for spike mass (2026-07-08)

## Hypothesis

R193 reduces the additive-spike part of the quarter-MGF route to the scalar
staircase-mass bound.  For the half-grid staircase this is controlled by

```text
exp(max(X)/4) / M.
```

R194 tests a simple logarithmic max law:

```text
max(X) ≤ 4 log M + C.
```

## Probe

File: `scripts/probes/probe_r194_log_max_spike_bound.py`.

The probe reports:

```text
maxX - 4 log M
exp(maxX/4) / M
```

on the exact R189 case set.

## Result

Default exact run:

```text
worst_defect = -5.435433
worst_ratio  = 0.256954
violations maxX <= 4 log M - 5: 0
```

The crude R191 infinite-bulk slack gives target

```text
exp(maxX/4) / M <= 0.199786
```

and only two tiny cases violate it:

```text
M = 16, ratio = 0.256954
M = 21, ratio = 0.209646
```

Cutoff sweep:

```text
M >= 32:   worst_ratio = 0.145620
M >= 64:   worst_ratio = 0.122146
M >= 128:  worst_ratio = 0.110991
M >= 1024: worst_ratio = 0.079722
```

## Verdict

The spike-mass side now has a plausible two-part proof strategy:

1. certify the finitely many tiny-index cases separately;
2. prove a uniform large-index logarithmic max bound, already empirically
   stronger than `maxX ≤ 4 log M - 5`.

At prize scale the spike ratio is far below the budget threshold.  The
high-spike adversarial rows are not the blocker after normalization by `M`;
the only blockers are very small coset-count base cases.
