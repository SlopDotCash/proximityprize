# #466 R261: level CDF envelope ordering

Date: 2026-07-09

## Question

R260 refutes simple arithmetic fingerprints. R261 asks whether the trim-five
residual CDF envelope is ordered by dyadic level, which would suggest a tower
or induction proof.

Command:

```bash
python3 scripts/probes/probe_r261_level_cdf_envelope_order.py --cache-only
```

## Result

Raw survival maxima:

```text
theta   all      n=256    n=512    n=1024
0.500   0.516414 0.516414 0.508772 0.501812
0.625   0.470960 0.470960 0.458090 0.450485
0.750   0.412121 0.407828 0.412121 0.405589
0.755   0.411765 0.405303 0.411765 0.404595
0.875   0.375000 0.375000 0.374411 0.368378
1.250   0.283544 0.280584 0.283544 0.282051
2.000   0.175439 0.171634 0.170515 0.175439
```

Winners by threshold:

```text
theta=0.500 winner n=256
theta=0.625 winner n=256
theta=0.750 winner n=512
theta=0.755 winner n=512
theta=0.875 winner n=256
theta=1.250 winner n=512
theta=2.000 winner n=1024
```

## Route update

There is no simple dyadic-level monotonicity. The envelope crosses:

- low thresholds are worst at `n=256`,
- the micro-band is worst at `n=512`,
- some high-tail points are worst at `n=1024`.

The R251 micro-band theorem may be finite-level local around `n=512`, but the
full residual tail cannot be proved by a naive “higher levels improve”
monotonicity argument.
