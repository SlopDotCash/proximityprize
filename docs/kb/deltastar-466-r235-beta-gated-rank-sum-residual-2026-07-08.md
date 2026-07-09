# R235: beta-gated rank-sum residual

Status: positive scaling evidence for the R234 proof socket.

## Question

R234 showed that a direct top-8 rank-sum cap plus residual half-band tail
closes after excluding the known `n=64` direct-MGF resonance rows.  R235 asks
whether a simpler large-index gate can replace delicate resonance
classification:

```text
M = (p - 1) / n >= n^(beta - 1)
```

with a finite/small-index branch for the remaining rows.

## Beta sweep

Command:

```bash
for beta in 0 2 3 4; do
  python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
    --medium-min-a 3 --medium-max-a 10 --medium-max-index 2500 \
    --min-index 2 --min-beta $beta --chunk 8192 \
    --trims 8 --taus 0.5 --spike-budgets 0 --top 3
done
```

Results:

```text
beta=0: best_budget=3.741282, fail
beta=2: best_budget=3.741282, fail
beta=3: best_budget=2.058460, fail by 0.05846
beta=4: best_budget=1.714614, pass with slack 0.285386
```

The beta-3 failure is caused by small-index rows:

```text
top witness:    n=8, p=521, M=65
budget witness: n=32, p=65537, M=2048
```

## Beta 3 plus finite M floor

Adding a modest finite branch `M >= 512` makes beta 3 pass.

Command:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 3 --medium-max-a 10 --medium-max-index 2500 \
  --min-index 512 --min-beta 3.0 --chunk 8192 \
  --trims 8 16 --taus 0.5 0.75 1.0 --spike-budgets 0 --top 10
```

Result:

```text
cases=1089
feasible_rows=6
best_budget=1.909360
slack=0.090640
topCap=0.176136
C_req=0.64951109
trim=8 tau=0.5 K=0
```

Witnesses:

```text
top-rank witness: n=32, p=32993, M=1031
C witness:        n=8,  p=17393, M=2174
budget witness:   n=32, p=65537, M=2048
```

## Interpretation

The strongest current large-index residual is:

```text
M >= 512 and M >= n^2
```

then prove:

```text
Top8RankMGFCap <= 0.177
ResidualHalfBandTail C <= 0.650 after removing top 8 ranks
```

This closes the tested `a=3..10`, `M<=2500` exact window with about `0.09`
slack.  Beta 4 is easier and may be a safer first theorem target; beta 3 plus
finite floor is sharper.

No prize closure is claimed.  The live decomposition becomes:

1. finite branch for `M < 512`;
2. beta-gated rank-sum residual for `M >= 512` and `M >= n^2`;
3. eventual extension from exact medium windows to the prize-scale index.
