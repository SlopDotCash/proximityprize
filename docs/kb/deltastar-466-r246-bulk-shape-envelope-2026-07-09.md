# #466 R246: trim-five bulk shape envelope

Date: 2026-07-09

## Question

R245 states the surviving residual socket as a direct vertical CDF theorem.
R246 asks whether the first-band endpoint is an isolated accident or part of a
stable bulk-shape envelope.

Command:

```bash
python3 scripts/probes/probe_r246_bulk_shape_envelope.py --cache-only
```

## Scaled survival envelope

For `S(theta) = #{x in R_5 : x >= theta} / M`, the cached main lane gives:

```text
theta   max_S    max S(theta) exp(theta/2)
0.500   0.516414 0.663089
0.625   0.470960 0.643725
0.750   0.412121 0.599633
0.875   0.375000 0.580811
1.000   0.339646 0.559982
1.125   0.309774 0.543671
1.250   0.283544 0.529730
1.500   0.237189 0.502129
1.750   0.201439 0.483227
2.000   0.175439 0.476892
2.500   0.128548 0.448675
3.000   0.094923 0.425414
```

The scaled half-rate envelope is monotone decreasing through the relevant
range. The current route starts at `theta = 0.75` exactly because the lower
band is too expensive:

```text
theta=0.625 requires C=0.643725
theta=0.750 requires C=0.599633
```

## Quantile equivalent

The first-band cap can be restated as a quantile theorem. The largest cached
residual quantiles are:

```text
q       max_Q
0.580   0.739516
0.590   0.762668
0.600   0.790489
0.610   0.825430
0.625   0.891357
0.650   0.969560
```

Thus the endpoint is nearly equivalent to a trim-five 60th-percentile cap:

```text
Q_0.60(R_5) <= 0.79049
```

or, in counting form,

```text
S(0.75) <= 0.4122.
```

## Route update

R246 strengthens R245: the residual theorem should be attacked as a stable
bulk-shape theorem, not as a single exceptional threshold. A clean sufficient
form is:

```text
for theta >= 0.75,
S(theta) exp(theta/2) is bounded by its first-band maximum <= 0.6012.
```

The quantile version `Q_0.60 <= 0.79049` may be the simpler first target,
because it isolates the middle-bulk cap without asking for the full tail at
once.
