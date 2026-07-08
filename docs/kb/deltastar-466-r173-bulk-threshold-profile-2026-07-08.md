# δ* #466 — bulk threshold profile near T=1 (2026-07-08)

## Hypothesis

R170/R172 showed the closed-form tail law is limited by bulk thresholds, not
high-tail exceptional cosets.  R173 measures the normalized coset distribution
near `T=1`.

Probe: `scripts/probes/probe_r173_bulk_threshold_profile.py`.

## Result

Representative mature rows:

```text
n   p          kind        q50    q67    q75    q90    maxX
------------------------------------------------------------------------------
64  16778497   spike       0.461  0.957  1.333  2.718  27.584
128 268437889  control     0.458  0.951  1.326  2.710  23.688
256 16777729   control     0.456  0.952  1.325  2.708  16.587
```

The bulk tail is extremely stable:

```text
T0.75: frac≈0.386..0.389, envelope=0.622
T0.90: frac≈0.343..0.345, envelope=0.599
T1.00: frac≈0.318..0.319, envelope=0.584
T1.10: frac≈0.295..0.296, envelope=0.570
T1.25: frac≈0.264..0.266, envelope=0.549
T1.50: frac≈0.221..0.222, envelope=0.515
T2.00: frac≈0.158..0.159, envelope=0.455
```

Worst row in this profile:

```text
worst_bulk_ratio=0.670912
n=512 p=262657 T=0.75 frac=0.417154 envelope=0.621772
```

At the key R170 threshold `T=1`, mature rows have

```text
N(1)/M ≈ 0.32,
(3/4) exp(-1/4) ≈ 0.584.
```

## Verdict

The bulk component is not close to violating the closed-form envelope.  It
looks like a stable limiting distribution with median around `0.46`, 75th
percentile around `1.33`, and 90th percentile around `2.71`.

Proof clue:

```text
It may be enough to prove a coarse bulk anti-concentration statement
  N(1) ≤ 0.5 M
plus a separate exponential high-tail estimate.
```

The current all-in-one envelope `(3/4)M exp(-T/4)` has large cushion at `T=1`.
The hard proof obligation is therefore not a numerically tight bulk bound, but
finding a structural argument that explains why only about one third of dyadic
cosets sit above the mean-square level.
