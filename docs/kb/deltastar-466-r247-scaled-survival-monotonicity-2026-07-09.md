# #466 R247: exact scaled-survival monotonicity refuted

Date: 2026-07-09

## Question

R246 suggested that the half-rate scaled survival

```text
H(theta) = S(theta) exp(theta/2)
```

decreases through the useful band after deleting the top five quotient values.
R247 checks this at every exact residual order-statistic jump, not merely on a
coarse threshold grid.

Command:

```bash
python3 scripts/probes/probe_r247_scaled_survival_monotonicity.py --cache-only
```

## Result

Literal monotonicity is false. There are many exact staircase violations,
caused by isolated residual spikes at high thresholds.

However, the worst global values of `H(theta)` over `theta >= 0.75` still occur
very close to the first band:

```text
Hmax     theta*    count* n     p          M
0.601109 0.756650  336    512   417793     816
0.600681 0.757821  498    512   620033     1211
0.600464 0.752769  612    512   760321     1485
0.595027 0.757585  209    512   262657     513
0.594231 0.752845  323    256   202753     792
```

This recovers the R238 endpoint exactly:

```text
max H(theta) = 0.601109 at theta = 0.756650
```

## Route update

The clean monotonicity conjecture from R246 is refuted. Replace it with the
weaker and accurate socket:

```text
TrimFiveResidualHalfRateSup:
  sup_{theta >= 0.75} S(theta) exp(theta/2) <= 0.6012.
```

This is equivalent to the residual half-rate CDF theorem from R245, but R247
clarifies that it cannot be proven by simple monotonicity of the empirical
staircase. Any proof must control both:

1. the first-band middle bulk, and
2. the isolated high residual spikes that cause local nonmonotone bumps.
