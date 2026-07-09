# R233 top-five budget cap diagnostics

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R231's current live residual is:

```text
trim = 5, tau = 0.75, K = 0, C ~= 0.6012.
```

R233 separates the exact top-five contribution from the residual envelope and
asks what uniform top-order-statistic cap is needed.

## Probe

New script:

```text
scripts/probes/probe_r233_top5_budget_cap.py
```

It reports:

- exact top-five staircase contribution per quotient carrier;
- exact top-five MGF contribution;
- residual envelope budget;
- total certificate budget;
- worst rows and simple normalized ratios.

## Cached `n >= 256` result

Command:

```bash
python3 -m py_compile scripts/probes/probe_r233_top5_budget_cap.py
python3 scripts/probes/probe_r233_top5_budget_cap.py --cache-only --top 20
```

Output summary on the current R231 cached subset:

```text
cases=1499
worst_total=1.995028
slack=0.004972
worst_top_stair=0.284384
topMGF=0.283696
worst_top row: n=512 p=566273 M=1106
worst_maxX=25.278818 at n=1024 p=2486273 M=2428
```

The residual budget is very stable around `1.71`; the dangerous quantity is
the top-five staircase contribution.  A theorem of the form

```text
top5_staircase_budget <= 0.284
```

would almost close the cached window, and a slightly rounder target

```text
top5_staircase_budget <= 0.28
```

would need either a slightly better residual constant or a sharper staircase.

## Finite exception at n = 128

A small exact sweep including `n=128`:

```bash
python3 scripts/probes/probe_r233_top5_budget_cap.py \
  --medium-min-a 7 --medium-max-a 8 --medium-max-index 1536 \
  --min-index 512 --cache-dir /tmp/proximity-r233-small --top 20
```

finds one large obstruction:

```text
n=128
p=65537
M=512
total=2.701602
topStair=0.988894
topMGF=0.985534
maxX=24.486519
fifth=8.903057
```

Neighboring `n=128` and `n=256` rows have wide slack.  This suggests the top-five
cap is a large-index/asymptotic lane with a finite exceptional Fermat row, not a
uniform small-parameter theorem.

## Interpretation

The R231/R233 live target is now:

```text
For n >= 256 in the prize-like quotient range:
  top5_staircase_budget <= about 0.284
  residual tail above tau=0.75 has C <= about 0.6012 and K=0
  total budget < 2.
```

This is much sharper than the earlier survival-envelope attempts.  It also
separates the two hard tasks:

- a top-order-statistic bound for the five largest quotient Gauss periods;
- a residual survival bound after deleting those five orbits.

The `n=128,p=65537` row should be treated as a finite base exception or as a
separate structured-prime obstruction.
