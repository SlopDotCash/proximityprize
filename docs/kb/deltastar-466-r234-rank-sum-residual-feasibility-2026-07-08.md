# R234: rank-sum residual feasibility

Status: first promising post-exception closure shape for the quotient-MGF route.

## Probe

Script:

```text
scripts/probes/probe_r234_rank_sum_residual_feasibility.py
```

It tests a sharper proof shape than R231:

```text
1. pay the top L quotient ranks by a direct MGF rank-sum cap;
2. prove a survival envelope only for the residual spectrum;
3. combine direct top-rank contribution with the residual staircase budget.
```

This is different from the failed R231 trimmed-tail route, which paid the top
spikes through a staircase count envelope and therefore overcharged them.

## Full medium window still fails

Command:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-max-a 8 --medium-max-index 2048 --min-index 512 --chunk 8192 \
  --trims 1 2 4 8 16 32 64 128 --taus 0.5 1.0 2.0 4.0 \
  --spike-budgets 0 1 2 --top 24
```

Summary:

```text
cases=1684
feasible_rows=0
best_budget=3.709096
topCap=1.981594
C_req=0.64611544
trim=16 tau=0.5 K=0
```

This failure is expected because the scan includes rows whose exact direct
MGF is already above the target `2`, especially `n=64, p=65537, M=1024`.

## Post-resonance window closes

After excluding the known direct-MGF resonance rows and testing only
`n=64, M >= 3194`, the direct rank-sum residual shape closes.

Command:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 6 --medium-max-a 6 --medium-max-index 10000 \
  --min-index 3194 --chunk 8192 \
  --trims 8 16 32 --taus 0.5 1.0 --spike-budgets 0 --top 12
```

Result:

```text
cases=1047
feasible_rows=2
best_budget=1.963225
slack=0.036775
topCap=0.235967
C_req=0.63476530
trim=8 tau=0.5 K=0

top-rank witness: n=64 p=421313 M=6583
C witness:        n=64 p=351361 M=5490
budget witness:   n=64 p=586433 M=9163
```

The later window `M >= 6001` is similarly feasible:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 6 --medium-max-a 6 --medium-max-index 10000 \
  --min-index 6001 --chunk 8192 \
  --trims 8 16 --taus 0.5 1.0 --spike-budgets 0 --top 8
```

Result:

```text
cases=608
feasible_rows=2
best_budget=1.961875
slack=0.038125
topCap=0.235967
C_req=0.63323354
trim=8 tau=0.5 K=0
```

## Interpretation

This is a useful positive signal.  A viable post-exception residual is:

```text
Top8RankMGFCap:
  sum_{r < 8} exp(X_(r)/4) / M <= 0.236

ResidualHalfBandTail:
  for the remaining quotient ranks,
  N_res(theta) <= 0.635 * M * exp(-theta/2),  theta > 1/2.
```

Together these close the staircase MGF budget with about `0.037` slack in the
tested post-resonance `n=64` windows.  The constants are empirical and should
not be frozen yet; the point is the proof shape.

The next mathematical attack should therefore split the quotient problem into:

1. a finite/direct branch for the exact MGF-failing resonance rows up to
   `M=3193`;
2. a top-8 rank-sum anti-concentration theorem for non-exceptional rows;
3. a residual half-band survival theorem after removing the top 8 ranks.

No prize closure is claimed.  R234 identifies a narrower residual that finally
closes numerically after the known direct counterexamples are removed.
