# R237 top-five scaling law

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

R233 reduced the live top-five branch to bounding

```text
top5_mass = sum_{i <= 5} exp(X_i / 4)
```

relative to quotient carrier `M`.  R237 tests simple normalizations to find a
theorem-shaped cap.

## Probe

New script:

```text
scripts/probes/probe_r237_top5_scaling_laws.py
```

It reports worst rows for:

```text
top5_mass / M
top5_mass / sqrt(M)
top5_mass / sqrt(M log M)
top5_mass / (log M)^2
top5_mass
```

## Main lane result, superseded by wider sweep

Command:

```bash
python3 -m py_compile scripts/probes/probe_r237_top5_scaling_laws.py
python3 scripts/probes/probe_r237_top5_scaling_laws.py --cache-only --top 12
```

Initial cached `n >= 256`, `M <= 4096` subset:

```text
cases=1499
max top5_mass / M = 0.28369567
max top5_mass / sqrt(M) = 12.28600414
max top5_mass / sqrt(M log M) = 4.40055572
max top5_mass / (log M)^2 = 9.96374182
```

This suggested the clean-looking scaling cap:

```text
top5_mass <= 4.5 * sqrt(M log M)
```

on that cached main lane.  This implies `top5_mass / M <= 4.5 * sqrt(log M / M)`,
so it becomes much stronger than the fixed `0.284` budget cap as `M` grows.

Worst main-lane row for this normalization:

```text
n=1024
p=2486273
M=2428
top5_mass=605.389659
top5_mass / sqrt(M log M)=4.40055572
```

## Wider sweep refutation

Follow-up command, rerun after hardening corrupt-cache handling in the shared
R231 helper:

```bash
python3 -m py_compile \
  scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  scripts/probes/probe_r237_top5_scaling_laws.py \
  scripts/probes/probe_r238_trim5_residual_tail.py
python3 scripts/probes/probe_r237_top5_scaling_laws.py \
  --medium-min-a 8 --medium-max-a 12 --medium-max-index 5000 \
  --min-index 512 --chunk 8192 --trim 5 --top 12
```

Result:

```text
cases=3098
max top5_mass / M = 0.33834486
max top5_mass / sqrt(M) = 16.01688681
max top5_mass / sqrt(M log M) = 5.54023116
max top5_mass / (log M)^2 = 14.97220689
```

Counterexample to the proposed `4.5 * sqrt(M log M)` cap:

```text
n=1024
p=4366337
M=4264
top5_mass=1045.891671
top5_mass / sqrt(M log M)=5.54023116
```

So the R237 `4.5` law is false on the wider exact quotient sweep.  A weaker
version with constant `5.6` survives this window, but its margin is not yet
credible enough to promote as a theorem-shaped target without a larger stress
test.

## n=128 check

Command:

```bash
python3 scripts/probes/probe_r237_top5_scaling_laws.py \
  --medium-min-a 7 --medium-max-a 8 --medium-max-index 4096 \
  --min-index 512 --cache-dir /tmp/proximity-r233-n128 \
  --cache-only --top 10
```

The two finite exceptions also stand out under this scaling:

```text
n=128 p=65537  M=512  top5_mass/sqrt(M log M)=8.92837622
n=128 p=231169 M=1806 top5_mass/sqrt(M log M)=5.604759
```

All other reported n=128 rows are below the main-lane margin or much closer to
it.

## Interpretation

The top-five branch can no longer be reframed with the `4.5` cap:

```text
Main lane:
  REFUTED: top5_mass <= 4.5 * sqrt(M log M)
  surviving observed window: top5_mass <= 5.6 * sqrt(M log M)
  plus residual tail after deleting top five.

Finite lane:
  discharge (128,65537,512) and (128,231169,1806) separately.
```

The route is still structurally interesting, but the attractive constant was a
cache-window artifact.  Any top-five theorem must either pay a larger
order-statistic constant or isolate the new `(1024,4366337,4264)` resonance as
part of the finite branch.
