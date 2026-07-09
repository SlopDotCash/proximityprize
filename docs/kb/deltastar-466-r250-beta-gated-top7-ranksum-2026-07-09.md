# R250 beta-gated top-seven rank-sum repair

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R237/R249 sharpened the trim-five residual side, but the top-five payment was
refuted on the wider exact window:

```text
n=2048 p=1417217 M=692
trim-five total budget = 2.050604
```

This row has very small quotient index relative to `n`; it is not on the
prize-diagonal branch where `p ~= n^beta` and `M=(p-1)/n >= n^2` for
`beta >= 3`.  R250 retests the rank-sum proof shape under the beta gate.

## Unrestricted trim sweep

Command:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --chunk 8192 --cache-dir .cache/proximity-r231 \
  --trims 5 6 7 8 9 10 12 16 \
  --taus 0.5 0.625 0.75 0.875 1.0 --spike-budgets 0 \
  --step 0.03125 --cutoff 0 --top 30
```

Result:

```text
feasible_rows=0
best_budget=2.050604
best row: trim=5 tau=0.75 C_req=0.60110935
budget witness: n=2048 p=1417217 M=692
```

Paying more ranks does not help on the unrestricted window; it increases the
direct top payment faster than it decreases the residual envelope.

## Beta-gated rank-sum sweep

Command:

```bash
python3 scripts/probes/probe_r234_rank_sum_residual_feasibility.py \
  --medium-min-a 3 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --min-beta 3.0 --chunk 8192 \
  --trims 5 6 7 8 9 10 12 16 \
  --taus 0.5 0.625 0.75 0.875 1.0 --spike-budgets 0 \
  --step 0.03125 --cutoff 0 --top 30
```

Result:

```text
cases=2586
feasible_rows=37
best_budget=1.879455
slack=0.120545
topCap=0.168534
C_req=0.65010210
trim=7
tau=0.5
```

Witnesses:

```text
top-rank cap:      n=32 p=32993  M=1031
residual C:        n=8  p=17393  M=2174, theta=0.501266, count=1100
budget witness:    n=64 p=296833 M=4638
```

The earlier top-eight `tau=0.75` route remains feasible, but the wider sweep
finds a stronger beta-gated target:

```text
top seven direct rank-sum cap <= 0.168534
residual after deleting top seven:
  S(theta) <= 0.65011 * exp(-theta/2) for theta > 0.5
quarter-MGF budget <= 1.87946
```

## Interpretation

The top-five failure is a low-index obstruction, not evidence against the
beta-gated prize-diagonal lane.  The current best quantitative socket is now:

```text
finite branch:
  discharge known small/bad resonance rows separately;

beta-gated branch M >= n^2:
  prove the top-seven rank-sum cap and residual half-rate tail above 0.5.
```

This is sharper than the previous top-eight beta-gated split and has about
`0.12` numerical budget slack on the tested exact window.
