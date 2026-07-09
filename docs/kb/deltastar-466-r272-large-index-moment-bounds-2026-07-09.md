# #466 R272: large-index moment bounds

Date: 2026-07-09

## Question

R268 reduces the large branch to the soft target

```text
M >= 1536 => S(0.75) <= 0.4055.
```

R272 asks whether ordinary variance/centered-moment inequalities are sufficient
for this softer cap.

Command:

```bash
python3 scripts/probes/probe_r272_large_index_moment_bounds.py --max-index 8000
```

## Result

Worst large-index rows:

```text
S        slack    mean     var      second   Markov2  Cantelli n     p          M
0.405233 0.000267 0.97303  1.59010  2.53688  4.510    1.000    1024  1604609    1567
0.403073 0.002427 0.98324  1.70238  2.66913  4.745    512   1299457    2538
0.402592 0.002908 0.97659  1.70456  2.65829  4.726    512   1264129    2469
```

Summary:

```text
S median=0.385815 p95=0.393974 max=0.405233
mean median=0.987961
var median=1.843360
Markov2 median=5.013319
Cantelli=1.0 (vacuous because mean > 0.75)
```

Correlations with `S`:

```text
mean       +0.149959
var        -0.457788
second     -0.400388
M/n        +0.092679
logM       +0.107339
```

## Route update

Ordinary moments remain the wrong proof interface, even for the softer
large-index cap. Since the residual mean is above `0.75`, upper-tail one-sided
variance inequalities are vacuous; raw Markov bounds are far too loose.

The large branch still needs a vertical lower-bulk distribution theorem, not a
standard variance/second-moment argument.
