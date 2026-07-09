# #466 R277: high-index q60 sufficient-condition search

Date: 2026-07-09

## Question

R276 leaves the high-index branch:

```text
M >= 2048 => q60(trim-five residual) <= 0.759
```

R277 asks whether this q60 cap follows from a smoother one-feature condition,
such as a lower-bulk partial average or partial sum.

## Probe

Script:

```text
scripts/probes/probe_r277_high_index_q60_sufficient_conditions.py
```

Full cached branch:

```text
python3 scripts/probes/probe_r277_high_index_q60_sufficient_conditions.py \
  --min-index 2048 --max-index 8000 --cache-only --top 12
```

Result:

```text
cases=2476 skipped=0
worst q60=0.75889031 at n=1024 p=3474433 M=3393
worst S(0.75)=0.40307329 at n=512 p=1299457 M=2538
```

Stratified higher-index sample:

```text
python3 scripts/probes/probe_r277_high_index_q60_sufficient_conditions.py \
  --min-index 8001 --max-index 20000 --stride 17 --limit-per-n 80 --top 10
```

Result:

```text
cases=240 skipped=0
worst sampled q60=0.74089036 at n=1024 p=9376769 M=9157
worst sampled S(0.75)=0.39630883 at the same case
```

## Signal

Lower-bulk quantities are the best smooth correlates:

```text
M in [2048,8000]:
  corr(q60, lowAvg75) = +0.849004
  corr(q60, lowSum75) = +0.848672
  corr(q60, lowSum70) = +0.843491
  corr(q60, lowAvg70) = +0.843446

sample M in [8001,20000]:
  corr(q60, lowSum70) = +0.862874
  corr(q60, lowAvg70) = +0.862471
  corr(q60, lowSum75) = +0.861925
  corr(q60, lowAvg75) = +0.861607
```

But no one-feature separator appears.  Tightening the artificial cap to
`q60 <= 0.758` leaves one bad point, and its partial sums lie inside the good
range for every tested feature.  The single-feature route is therefore not a
proof path.

## Updated route

R277 supports a two-stage close:

```text
2048 <= M <= 8000:
  finite certificate branch, analogous to R269/R275

M > 8000:
  analytic asymptotic branch
  target can be relaxed to q60 <= 0.741 on observed samples,
  or S(0.75) <= 0.397 on observed samples
```

The analytic branch should use coupled lower-bulk control, not an isolated
partial-sum cap.  A plausible next theorem shape is a Lorenz-window inequality:

```text
low-bulk mass at 70-75% plus a vertical spacing/Paley regularity estimate
  => q60 <= 0.759
```

For the prize route, the more mechanical option is stronger:

```text
finite certify through M=8000,
then prove an asymptotic q60 cap for M>8000 with the large-sieve/BGK substrate.
```
