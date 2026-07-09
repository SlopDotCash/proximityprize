# R240 residual tail by dyadic level

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R238/R239 identified the residual first band after deleting top five as the
live tail obstruction.  R240 groups the residual tail constants by dyadic level
`n` to see whether the obstruction worsens with the tower or is finite-level.

## Probe

New script:

```text
scripts/probes/probe_r240_residual_tail_by_level.py
```

It reports, for each threshold `theta`, the worst scaled residual tail

```text
(N_res(theta) / M) * exp(theta / 2)
```

overall and separately by `n`.

## Result

Command:

```bash
python3 -m py_compile scripts/probes/probe_r240_residual_tail_by_level.py
python3 scripts/probes/probe_r240_residual_tail_by_level.py --cache-only
```

Cached main-lane levels:

```text
n in {256, 512, 1024}
cases=1499
```

Worst scaled constants:

```text
theta=0.75:
  all    0.599633  n=512  p=760321  M=1485
  n=256  0.593387
  n=512  0.599633
  n=1024 0.590129

theta=0.80:
  all    0.590078  n=512  p=620033  M=1211

theta=0.875:
  all    0.580811  n=256  p=202753  M=792

theta=1.00:
  all    0.559982  n=256  p=202753  M=792

theta=1.25:
  all    0.529730  n=512  p=606721  M=1185

theta=1.50:
  all    0.502129  n=512  p=349697  M=683

theta=2.00:
  all    0.476892  n=1024 p=642049  M=627
```

## Interpretation

The first-band obstruction is not monotone-worsening with `n`.  In the cached
main-lane window:

- `n=512` controls the knife-edge `theta=0.75`;
- `n=256` controls the mid band around `theta=0.875` and `1.0`;
- `n=1024` only appears as worst at `theta=2.0`, where the target has large
  slack.

This supports the current split: the residual CDF theorem can be level-uniform
with constant `0.6012`, but the proof should focus on the first quantile band
rather than high-tail spikes.
