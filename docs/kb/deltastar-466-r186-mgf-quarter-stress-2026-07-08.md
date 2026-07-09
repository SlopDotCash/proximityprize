# δ* #466 — stress test for MGF(1/4) ≤ 2 (2026-07-08)

## Hypothesis

R185 shows that a child-side `MGF(1/4) ≤ 2` bound is sufficient for the
AM-GM dyadic tower route.  R186 stress-tests this residual directly.

Probe: `scripts/probes/probe_r186_mgf_quarter_stress.py`.

## Result

Across 122 exact dyadic spectra:

```text
violations_mgf1/4_le_2 = 0
worst_mgf1/4 = 1.523404 at n=32 p=32993
```

Worst rows:

```text
mgf1/4  mgf1/3  n    p          cosets    maxX    label
--------------------------------------------------------------------------------------
1.5234  2.1622  32   32993      1031      17.636  r63-spike
1.4670  1.9923  512  262657     513       16.168  r172-high
1.4467  1.8103  128  19073      149       10.932  grid-start=16384
1.4363  1.7323  32   1217       38        6.843   grid-start=1024
1.4221  1.7538  256  70657      276       11.625  grid-start=65536
1.4166  1.7580  64   264769     4137      18.030  grid-start=262144
1.4139  1.7660  64   16778497   262164    27.584  r63-spike
1.4112  1.7181  128  2101249    16416     18.320  r63-small-spike
1.4101  1.7126  128  268437889  2097171   23.688  r63-control
1.4090  1.7013  256  16777729   65538     16.587  r172-control
```

The more aggressive rate `1/3` is not safe:

```text
worst_mgf1/3 = 2.162206
```

## Verdict

`MGF(1/4) ≤ 2` is now the cleanest empirical residual for the tower route.
It is strong enough for R185 and has large measured slack.  Rate `1/3` is too
aggressive because the adversarial `n=32, p=32993` spike already exceeds `2`.

Current proof target:

```text
For dyadic periods, prove
  (1/M) Σ_C exp((|η_C|²/σ²)/4) ≤ 2.
```

Then R185 gives the tower product budget and R168/S11 gives the prize-route
moment envelope.
