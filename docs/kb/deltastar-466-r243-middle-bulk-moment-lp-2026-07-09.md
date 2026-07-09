# #466 R243: middle-bulk moment LP refutation

Date: 2026-07-09

## Question

R242 localized the live trim-five residual endpoint to a middle-bulk CDF cap:

```text
P[X_res >= 0.75] <= about 0.4122.
```

R243 asks whether this cap can be certified from low moments plus the exact
post-trim maximum. For each cached spectrum, it solves a discretized LP:

```text
maximize P[X >= 0.75]
subject to X in [0, max_residual],
           E[X^j] = exact residual moment_j, 1 <= j <= d.
```

Command:

```bash
python3 scripts/probes/probe_r243_middle_bulk_moment_lp.py --cache-only --top 8
```

## Result

Worst rows:

```text
surv     LPd2    LPd3    LPd4    cap      mean     second   M      n     p
0.412121 1.00000 0.76266 0.71057 8.918    0.96965  2.46573  1485   512   760321
0.412056 1.00000 0.76720 0.69949 8.395    0.96497  2.45056  1211   512   620033
0.411765 0.95375 0.74257 0.69204 6.627    0.95986  2.32019  816    512   417793
0.407828 0.99042 0.77326 0.70901 7.772    0.94883  2.26008  792    256   202753
```

Summary gaps between LP upper bound and true survival:

```text
degree=2 min_gap=0.469887 median_gap=0.609153 max_gap=0.637868
degree=3 min_gap=0.304676 median_gap=0.362970 max_gap=0.410754
degree=4 min_gap=0.265352 median_gap=0.304563 max_gap=0.342647
```

Even with degree-four moments and the exact residual maximum, the LP still
permits about `0.69-0.71` survival in the worst rows, far above the needed
`0.4122`.

## Route update

The first-band cap is not a low-moment theorem. It needs structure beyond
one-dimensional moment data: Fourier order, additive constraints, quotient
geometry, or a direct middle-bulk inequality for Gauss-period spectra.

This refutes attempts to prove R238/R241 through mean/variance/fourth-moment
survival estimates, even with optimistic post-trim box constraints.
