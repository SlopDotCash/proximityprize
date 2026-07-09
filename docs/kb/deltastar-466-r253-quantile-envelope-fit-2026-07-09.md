# #466 R253: quantile envelope fit

Date: 2026-07-09

## Question

R252 refuted local value-spacing rigidity near `0.75`. R253 asks whether the
micro-band cap is better expressed as a global quantile envelope for the
trim-five residual spectrum.

Command:

```bash
python3 scripts/probes/probe_r253_quantile_envelope_fit.py --cache-only
```

## Result

Quantile maxima on the cached main lane:

```text
p       maxQ
0.500   0.539212
0.525   0.621881
0.550   0.678873
0.575   0.731591
0.600   0.790489
0.625   0.891357
0.650   0.969560
0.700   1.168413
0.750   1.428030
0.800   1.757522
0.900   2.965569
```

Worst micro-band rows:

```text
micro    q60      q60/q50  q70/q60  n     p          M
0.601134 0.790489 1.54067  1.40189  512   760321     1485
0.601039 0.783391 1.55572  1.39419  512   620033     1211
0.600614 0.779684 1.52175  1.39007  512   417793     816
```

Correlations with the micro-band score:

```text
q60      +0.937601
q60/q50  +0.143578
q70/q60  -0.489534
q70-q50  +0.253991
```

## Route update

The micro-band cap is best phrased as a quantile theorem:

```text
TrimFiveQ60:
  Q_0.60(R_5) <= 0.79049
```

for the main lane `n >= 256`. Shape ratios such as `q60/q50` or `q70/q60` do
not explain the obstruction, so a one-parameter shape theorem is not the right
proof interface. The useful object is the absolute vertical quantile envelope.
