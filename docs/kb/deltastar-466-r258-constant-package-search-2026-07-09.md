# #466 R258: rounded constant package search

Date: 2026-07-09

## Question

R257 splits

```text
S(0.75) <= S(hi) + mass([0.75, hi)).
```

R258 asks whether the two terms can be bounded independently with clean rounded
constants while preserving the R251 budget:

```text
(A + B) * exp(0.755/2) <= 0.6012.
```

Command:

```bash
python3 scripts/probes/probe_r258_constant_package_search.py --cache-only
```

## Result

No independent rounded package survives. Best attempt with `1e-4` rounding:

```text
hi       pkgCost  pkgSlack direct   A       B
0.79049  0.618315 -0.017115 0.601134 0.3987  0.0252
0.81000  0.618606 -0.017406 0.601134 0.3915  0.0326
0.77000  0.619773 -0.018573 0.601134 0.4068  0.0181
```

The direct worst `S(0.75)` still costs only

```text
0.601134
```

but the independent maxima of `S(hi)` and the thin-band mass occur on different
rows, so their sum loses all slack.

## Route update

The q60-plus-thin-band decomposition is useful for understanding, but not as
two independent analytic lemmas. The theorem must control the coupled sum

```text
S(0.75)
```

directly, or prove a coupled tradeoff between `S(hi)` and
`mass([0.75,hi))`. Independent rounded caps are too lossy.
