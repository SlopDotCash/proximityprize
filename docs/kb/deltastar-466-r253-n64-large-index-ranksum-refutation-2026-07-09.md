# R253 n=64 large-index rank-sum refutation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R252 left a beta-gated rank-sum certificate alive through `M <= 8000`, with
the new witness `(n,p,M)=(64,421313,6583)`.  R253 asks whether this is a
sporadic finite-window obstruction or the start of a larger `n=64`
large-index resonance family.

## Signature check

Command:

```bash
python3 scripts/probes/probe_r232_top_spike_signature.py \
  --top 20 --chunk 8192 \
  --row 64,421313,n64-new-topcap \
  --row 64,400321,n64-residual-spike \
  --row 64,296833,n64-old-budget \
  --row 64,204353,n64-direct-mgf-fail
```

The new witness has a broad top cluster:

```text
n=64 p=421313 M=6583
top values:
26.099509 22.355181 21.595893 19.904283 17.763203 17.606167
14.951868 13.543893 13.335683 13.218486 ...
mgf1/4=1.667023
```

As in R232, negation is already quotient-collapsed and inversion does not
preserve the top set.  No cheap inverse/negation classifier appears.

## n=64 extended sweep

Command:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 6 --medium-max-a 6 --medium-max-index 12000 \
  --min-index 512 --min-beta 3.0 --chunk 8192 \
  --trims 8 10 12 16 \
  --taus 0.5 0.625 0.75 --spike-budgets 0 \
  --step 0.03125 --cutoff 0 --top 30
```

Result:

```text
cases=1216
feasible_rows=0
best_budget=3.238586
slack=-1.238586
topCap=0.724250
C_req=1.56899646
trim=16
tau=0.75
```

New dominant witness:

```text
top/budget witness:
  n=64 p=697601 M=10900

residual-C witness:
  n=64 p=665857 M=10404
  theta=13.218679
```

The top-eight row is even worse:

```text
trim=8 tau=0.75
budget=3.7612
C_req=2.25416
```

## Interpretation

The beta-gated rank-sum route is a finite-window artifact unless it gains a
new exception/classification branch for `n=64` large-index resonances.  Merely
paying more top ranks is not enough: by `M <= 12000`, even paying top 16 leaves
the residual tail constant and direct top cap far above budget.

The next viable hypothesis must be structural, e.g.

```text
classify/remove n=64 large-index resonance families,
or replace rank-sum CDF control by an exact resonance decomposition.
```

The previous R252 top-eight target should no longer be treated as a stable
asymptotic socket.
