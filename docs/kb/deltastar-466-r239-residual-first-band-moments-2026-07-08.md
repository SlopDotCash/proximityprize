# R239 residual first-band moments

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R238 showed the residual tail after deleting the top five is tight at the first
live threshold `theta = 0.75`.  R239 asks whether this first-band cap follows
from low moments of the residual spectrum.

## Probe

New script:

```text
scripts/probes/probe_r239_residual_first_band_moments.py
```

For each cached exact spectrum it reports:

- residual fraction above `theta = 0.75`;
- scaled tail quantity `(N_res(theta)/M) * exp(theta/2)`;
- residual mean;
- residual second moment;
- residual quarter-MGF;
- first residual maximum after deleting top five.

## Result

Command:

```bash
python3 -m py_compile scripts/probes/probe_r239_residual_first_band_moments.py
python3 scripts/probes/probe_r239_residual_first_band_moments.py --cache-only --top 20
```

Summary on the cached `n >= 256` subset:

```text
cases=1499
worst_scaled=0.59963283
worst row: n=512 p=760321 M=1485
frac_above_0.75=0.41212121
max_mean=0.98908126
max_second=3.02669177
max_residual_mgf1/4=1.40642036
```

Top rows have residual fractions around `0.40-0.412` above `0.75`.

## Interpretation

Low moments do not explain the first-band cap.  For example:

```text
mean / 0.75 > 1
second / 0.75^2 > 4
mgf1/4 * exp(-0.75/4) > 1
```

so Markov-style bounds from these quantities are vacuous at the critical
threshold.  The needed input is a genuine CDF/anti-concentration statement for
the residual quotient spectrum:

```text
after deleting top five,
#{X >= 0.75} / M <= about 0.4122
```

and the rest of the exponential tail has increasing slack.

This focuses the analytic task: prove the first residual quantile band, not a
generic moment consequence.
