# #466 R249: finite multiband residual certificate

Date: 2026-07-09

## Question

R248 showed that a coarse two-component certificate fails: a first-band cap at
`theta = 0.75` cannot control all of `[0.75, 0.875)` by raw survival
monotonicity.

R249 searches for a finite band certificate. For thresholds

```text
0.75 = t_0 < t_1 < ... < t_k
```

use:

```text
S(theta) <= S(t_i) for theta in [t_i, t_{i+1})
S(theta) exp(theta/2) <= C_tail for theta >= t_k.
```

Each finite band costs `S(t_i) exp(t_{i+1}/2)`.

## Result

Coarse bands fail. The first safe endpoint is a micro-band:

```text
python3 scripts/probes/probe_r249_multiband_residual_certificate.py \
  --cache-only \
  --candidates 0.755 0.76 0.765 0.77 0.775 0.785 0.8 0.825 0.85 0.875 0.9 1.0 \
  --max-extra 5 --top 12
```

Best grid:

```text
bands=(0.75, 0.755)
cost=0.60113378
slack=0.00006622
```

Details:

```text
kind  theta    next   cost      S_cap    tailTheta count  n     p          M
band  0.750    0.755  0.601134  0.412121 -         -      512   760321     1485
tail  0.755    inf    0.601109  -        0.756650  336    512   417793     816
```

The first-band cap is `S(0.75) = 612/1485 = 0.4121212121`. Against target
`C = 0.6012`, raw survival monotonicity is safe only up to

```text
2 log(0.6012 / (612/1485)) = 0.7552202952.
```

Thus `0.755` is essentially the largest simple endpoint with positive slack.

## Route update

The residual CDF socket can now be split into two finite theorem obligations:

1. **Micro-band bulk cap**

   ```text
   S(0.75) <= 612/1485
   ```

   or a rounded theorem-grade cap strong enough to imply
   `S(0.75) exp(0.755/2) <= 0.6012`.

2. **High-tail half-rate cap from 0.755**

   ```text
   sup_{theta >= 0.755} S(theta) exp(theta/2) <= 0.6012.
   ```

This split is still knife-edge, but it is simpler than proving the full
residual envelope in one stroke. It isolates the only interval where monotone
survival loses budget: `[0.75, 0.755)`.
