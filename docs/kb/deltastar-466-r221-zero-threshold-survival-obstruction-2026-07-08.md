# δ* #466 — R221 zero-threshold survival obstruction

R217/R216 used the half-rate-looking normalized-square survival envelope

```text
#{X_b >= θ} <= 0.6 * M * exp(-θ/2) + 2
```

as a candidate input for the finite-grid MGF consumer, where

```text
X_b = |η_G(b)|^2 / σ^2.
```

R221 checks the envelope itself, not just the weighted budget.

## Probe

Artifact:

```text
scripts/probes/probe_r221_survival_envelope_optimizer.py
```

Prize-style run:

```text
python3 scripts/probes/probe_r221_survival_envelope_optimizer.py \
  --mode prize --ns 64 128 256 512 --samples 20000 --seed 466221 \
  --step 0.25 --cutoff 24 --scales 1 1.5 2 2.5 3 \
  --c-bulk 0.6 --scale 2 --spike-budget 2
```

Readout:

```text
live_envelope_worst_ratio=2.079938 n=128
required_C scale=2 C=1.247963 theta=20.250 n=128
```

Exact-anchor run:

```text
python3 scripts/probes/probe_r221_survival_envelope_optimizer.py \
  --mode exact --max-n 256 --max-p 350000000 \
  --step 0.25 --cutoff 24 --scales 1 1.5 2 2.5 3 \
  --c-bulk 0.6 --scale 2 --spike-budget 2
```

Readout:

```text
live_envelope_worst_ratio=1.666664 n=128 p=268437889
required_C scale=2 C=0.999999 theta=0.000 n=128
```

## Correction

The literal envelope cannot include `θ = 0`: every carrier point survives at
zero, while the bound gives only `0.6 M + 2`.  For the prize-index carrier,
`2` is negligible, so the hypothesis is false before any hard analytic input
is considered.

Lean artifact:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R221ZeroThresholdSurvivalObstruction.lean
```

It proves:

```text
full_carrier_le_tail_at_zero
threeFifths_zero_tail_forces_spike_budget
```

The second theorem says the `(3/5, K)` envelope can contain zero only if

```text
(2/5) * M <= K.
```

## Next target

The R216 finite-grid consumer is still sound.  The corrected route must split
the layer cake:

1. pay the `θ = 0` bin exactly with `B(0) = M`;
2. apply a bulk-plus-spikes exponential envelope only for positive thresholds;
3. re-optimize the weighted budget under that split.

This is not cosmetic: R218 already showed that moment Markov does not prove the
low/mid-threshold law, and R221 now shows the previous literal survival law was
impossible at the first grid point.
