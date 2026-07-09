# δ* #466 — spike-budget decomposition for R189/R190 (2026-07-08)

## Hypothesis

R190 reduces `DyadicQuarterMGFBound` to a weighted grid budget for the R189
tail envelope

```text
N(T) ≤ (3/5) M exp(-T/2) + 2.
```

R191 separates that budget into:

- an infinite-grid bulk constant;
- an additive spike/max term controlled by `exp(max(X)/4) / M`.

## Probe

File: `scripts/probes/probe_r191_spike_budget_decomposition.py`.

The probe reuses the exact R189 spectra and computes:

```text
infinite_bulk_constant = exp(1/8)
  + (3/5) Σ_{j≥2} (exp(j/8)-exp((j-1)/8)) exp(-j/4)
```

and the observed scalar spike ratio:

```text
exp(max(X)/4) / M.
```

## Result

```text
infinite_bulk_constant     = 1.600428922910
infinite_bulk_slack_to_2   = 0.399571077090
worst_spike_ratio          = 0.256954
worst_budget               = 1.819292
```

Worst rows by spike ratio:

```text
exp(max/4)/M  budget  maxX   M       n   p          label
------------------------------------------------------------------------------------
0.256954      1.8193  5.65   16      16  257        grid-start=257
0.209646      1.7353  5.93   21      16  337        grid-start=257
0.157546      1.6055  4.97   22      16  353        grid-start=257
0.145620      1.7038  6.84   38      32  1217       grid-start=1024
0.131736      1.6683  6.23   36      32  1153       grid-start=1024
0.122146      1.7302  8.86   75      64  4801       grid-start=4096
0.110991      1.7992  16.17  513     512 262657     r172-high
0.079722      1.7457  17.64  1031    32  32993      r63-spike
```

## Verdict

The weighted-budget obligation in R190 can likely be replaced by a cleaner
two-part analytic target:

1. prove the bulk survival law `N(T) ≤ (3/5) M exp(-T/2) + 2`;
2. prove a logarithmic max bound strong enough to keep
   `exp(max(X)/4) / M` uniformly below the remaining slack.

The adversarial high-spike rows are not the worst spike-budget rows after
normalizing by `M`; the worst cases are very small coset counts.  At prize
scale, the spike term appears heavily suppressed.
