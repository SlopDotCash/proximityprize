# #466 R255: exponential order-statistic model

Date: 2026-07-09

## Question

R253 suggests the micro-band cap is essentially a `q60` theorem. R255 compares
the trim-five residual quantiles against the random complex-Gaussian model,
where normalized squared magnitudes would be approximately `Exp(1)`.

Command:

```bash
python3 scripts/probes/probe_r255_exponential_order_stat_model.py --cache-only
```

## Result

For `Exp(1)`, the ascending 60th percentile is

```text
-log(0.4) = 0.916290732
```

Worst micro-band rows:

```text
micro    q60      q60-exp  q60/mean mean     S075     n     p          M
0.601134 0.790489 -0.125802 0.81523  0.96965  0.412121 512   760321     1485
0.601039 0.783391 -0.132900 0.81183  0.96497  0.412056 512   620033     1211
0.600614 0.779684 -0.136607 0.81229  0.95986  0.411765 512   417793     816
```

Summary:

```text
q60     median=0.705132 p95=0.743031 max=0.790489
q60-exp median=-0.211159 p95=-0.173259 max=-0.125802
mean    median=0.977750 p95=0.986493 max=0.989081
```

Even the worst observed residual `q60` is substantially below the exponential
model's `q60`, while the residual mean remains near one. The missing middle
mass is compensated by the upper tail.

## Route update

The micro-band theorem should not be attacked as an exponential-tail theorem.
It is closer to a zero-heavy / mass-transport statement:

```text
after deleting the top five,
enough mass is forced below 0.75 (or below q60 <= 0.79049),
while the mean is restored by the upper residual tail.
```

This reframes the q60 cap as a lower-bulk dominance theorem, not as a Gaussian
upper-tail estimate.
