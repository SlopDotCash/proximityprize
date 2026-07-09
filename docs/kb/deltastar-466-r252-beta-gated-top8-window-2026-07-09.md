# R252 beta-gated top-eight widened window

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R250 found a strong beta-gated top-seven rank-sum certificate through
`M <= 5000`.  R252 asks whether that remains stable when the exact window is
expanded to `M <= 8000`.

## Command

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 3 --medium-max-a 12 --medium-max-index 8000 \
  --min-index 512 --min-beta 3.0 --chunk 8192 \
  --trims 7 8 10 12 \
  --taus 0.5 0.625 0.75 --spike-budgets 0 \
  --step 0.03125 --cutoff 0 --top 20
```

## Result

```text
cases=4586
best_budget=1.948854
slack=0.051146
topCap=0.235967
C_req=0.64951109
trim=8
tau=0.5
```

Witnesses:

```text
top-rank cap:   n=64 p=421313 M=6583
residual C:     n=8  p=17393  M=2174, theta=0.501266, count=1099
budget witness: n=64 p=421313 M=6583
```

The previous `trim=7` target weakens substantially:

```text
trim=7, tau=0.5: budget=1.9684, slack=0.0316
trim=7, tau=0.75: budget=2.0058, refuted in this window
```

The obstruction is a larger-index resonance at `(64,421313,6583)`; it becomes
both the top-cap and budget witness.

## Route update

For the beta-gated branch `M >= n^2`, the safer live target is now:

```text
pay top 8 ranks directly;
prove residual half-rate tail above tau=0.5 with C <= 0.64952;
finite exact window budget <= 1.94886.
```

The slack is still positive but much thinner than R250.  This suggests the
next attack should classify or bound the `n=64` large-index spike family rather
than simply increasing the number of paid ranks.
