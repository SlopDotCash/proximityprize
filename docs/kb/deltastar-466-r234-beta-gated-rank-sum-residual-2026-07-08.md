# R234: beta-gated rank-sum residual feasibility

Issue: #466. Date: 2026-07-08.

## Question

R233 showed that sorted-rank control separates the top-spike obstruction from
ordinary bulk, but a summable all-rank law is false.  R234 tests the resulting
two-component proof shape:

```text
pay the top L quotient ranks directly,
then prove an exponential residual-tail envelope only below rank L.
```

This is sharper than R231, which paid top spikes through the same staircase
survival budget and was killed by thin-regime Fermat rows.

## Probe

Updated script:

```text
scripts/probes/probe_r234_rank_sum_residual_feasibility.py
```

The script now supports:

```text
--min-beta β
```

which enforces `m = (p-1)/n >= n^(β-1)`.  This matters because the previous
unfiltered witness `n=64, p=65537, m=1024` has `p < n^3`; it is a thin-regime
artifact for the prize-facing quotient residual.

Compile check:

```text
python3 -m py_compile scripts/probes/probe_r234_rank_sum_residual_feasibility.py
```

## Unfiltered baseline

Command:

```text
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-max-a 8 --medium-max-index 2048 --min-index 512 --chunk 8192 \
  --trims 1 2 4 8 16 32 64 128 \
  --taus 0.5 1.0 2.0 4.0 --spike-budgets 0 1 2 --top 24
```

Result:

```text
cases=1684
feasible_rows=0
best_budget=3.709096
slack=-1.709096
topCap=1.981594
C_req=0.64611544
trim=16
tau=0.5
K=0
top witness: n=64, p=65537, M=1024
```

The unfiltered route fails because the thin Fermat row spends essentially the
entire budget in its top ranks before the residual is even counted.

## Beta >= 3 sweep

Command:

```text
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-max-a 8 --medium-max-index 4096 --min-index 512 --min-beta 3 \
  --chunk 8192 --trims 1 2 4 8 16 32 64 128 \
  --taus 0.5 1.0 2.0 4.0 --spike-budgets 0 1 2 --top 24
```

Result:

```text
cases=1956
feasible_rows=5
best_budget=1.909360
slack=0.090640
topCap=0.176136
C_req=0.64951109
trim=8
tau=0.5
K=0
top witness: n=32, p=32993, M=1031
C witness:   n=8,  p=17393, M=2174
budget witness: n=32, p=65537, M=2048
```

## Beta >= 4 stress

Affordable exact stress:

```text
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-max-a 5 --medium-max-index 8192 --min-index 512 --min-beta 4 \
  --chunk 8192 --trims 1 2 4 8 16 32 64 \
  --taus 0.5 1.0 2.0 --spike-budgets 0 1 --top 20
```

Result:

```text
cases=2173
feasible_rows=30
best_budget=1.737817
slack=0.262183
topCap=0.011587
C_req=0.66229220
trim=1
tau=0.5
K=0
top witness: n=8, p=4129, M=516
C witness:   n=8, p=4177, M=522
budget witness: n=16, p=128449, M=8028
```

## Interpretation

The rank-sum plus residual-tail route is refuted without a beta gate, but
becomes feasible in the prize-shaped window:

- the thin `n=64, p=65537` top-spike row is outside `p >= n^3`;
- after imposing `β >= 3`, the direct top-rank cost is only `0.176` at the
  best row and the total budget fits below `2`;
- in the deeper `β >= 4` stress, the best direct top-rank cost drops to
  `0.0116` and the total budget has `0.262` slack.

This suggests a viable next Lean residual:

1. a beta-gated direct top-rank cap for the first `L` quotient orbits;
2. a residual half-rate quotient-tail law after deleting those `L` orbits;
3. a deterministic consumer combining those two inputs into the existing
   quarter-MGF/prize endpoint.

No prize closure is claimed, but this is the first tested quotient-MGF shape
after R230/R231 with positive budget slack in the intended beta window.
