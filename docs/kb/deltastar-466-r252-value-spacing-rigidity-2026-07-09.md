# #466 R252: value-spacing rigidity near the micro-band

Date: 2026-07-09

## Question

R251 leaves a very tight main-lane micro-band cap

```text
S(0.75) * exp(0.755/2) <= 0.6012.
```

R244 ruled out obvious quotient-index structure. R252 asks whether the cap is
explained by value-space rigidity near the `0.75` boundary: gaps,
short-window densities, or local order-statistic slopes.

Command:

```bash
python3 scripts/probes/probe_r252_value_spacing_rigidity.py --cache-only
```

## Result

Worst rows:

```text
micro    S075     S755     edgeGap  cutGap   w005    w010    w020    n     p          M
0.601134 0.412121 0.410101 0.004604 0.003629 0.002020 0.003367 0.005387 512   760321     1485
0.601039 0.412056 0.411230 0.002024 0.006777 0.000826 0.001652 0.008258 512   620033     1211
0.600614 0.411765 0.411765 0.012124 0.012124 0.000000 0.001225 0.006127 512   417793     816
```

Correlations with the micro-band score:

```text
S075     +1.000000
S755     +0.994025
edgeGap  -0.191625
cutGap   -0.215454
w005     +0.043782
w010     +0.105142
w020     +0.154300
w050     +0.201958
w100     +0.327401
slope4   -0.038295
slope8   -0.035289
slope16  -0.078773
slope32  -0.146864
```

There is no useful value-spacing rigidity at the boundary. Local gaps and
order-statistic slopes are weakly anti-correlated with the obstruction.

## Route update

The micro-band cap is not likely to be proved via a local spacing/gap argument
around `0.75`. It remains a genuine bulk-count theorem:

```text
#{x in R_5 : x >= 0.75} <= 0.4122 M
```

Any proof should target global vertical distribution rather than local
boundary regularity.
